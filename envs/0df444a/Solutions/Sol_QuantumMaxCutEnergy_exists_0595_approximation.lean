-- Prove2me | solution 1 for QuantumMaxCutEnergy.exists_0595_approximation
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-01T15:06:52.56159+00:00
-- url     : https://prove2.me/submissions/7a7772de-1233-4ac3-8438-4f364f9485cb
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_QuantumMaxCutEnergyEstimationModel
import Definitions.Def_QuantumMaxCutFiniteNumericRuntime
import Definitions.Def_QuantumMaxCutPauliMomentRelaxationModel
import Theorems.Thm_QuantumMaxCutEnergy_scaled_bounds
import Theorems.Thm_QuantumMaxCutEnergy_PauliSDP_uniform_value_lower_approximation_compiler
import Theorems.Thm_QuantumMaxCutEnergy_PauliSDP_strict_gap_0595
import Mathlib

noncomputable section
open scoped BigOperators

namespace QuantumMaxCutEnergy.PauliSDP
open OAI.MetricKMedian.Binary

def scaledMachine (γ : ℚ≥0) (B : Algorithm) : Algorithm where
  randomFactor := 0
  randomDegree := 0
  run G r := γ * B.run G r

def scaledRationalProgram (γ : ℚ≥0) (B : Algorithm)
    (P : PolyProgram encodeRequest Ratio.encode
      (fun req : Input × List Bool => (B.run req.1 req.2 : ℚ))) :
    PolyProgram encodeRequest Ratio.encode
      (fun req : Input × List Bool => ((scaledMachine γ B).run req.1 req.2 : ℚ)) :=
  (((PolyProgram.constant encodeRequest Ratio.encode (γ : ℚ)).fanout P).comp
    PolyProgram.ratMul).congr _ (fun _ => by simp [scaledMachine])

theorem scaledMachine_polynomialTime (γ : ℚ≥0) (B : Algorithm)
    (P : PolyProgram encodeRequest Ratio.encode
      (fun req : Input × List Bool => (B.run req.1 req.2 : ℚ))) :
    PolynomialTime (scaledMachine γ B) := by
  let R : PolyProgram encodeRequest (fun q : ℚ≥0 => Ratio.encode (q : ℚ))
      (fun req : Input × List Bool => (scaledMachine γ B).run req.1 req.2) :=
    (scaledRationalProgram γ B P).recode id (fun _ => rfl) (fun _ => rfl)
  exact ⟨(R.comp QMCNumericRuntime.nnratOutput).stock⟩

theorem scaledMachine_ratio (γ : ℚ≥0) (B : Algorithm) (α : ℝ)
    (h : ∀ G : Input,
      ((γ * B.run G [] : ℚ≥0) : ℝ) ≤ optimum G ∧
        α * optimum G ≤ ((γ * B.run G [] : ℚ≥0) : ℝ)) :
    ApproximationRatio (scaledMachine γ B) α := by
  intro G
  change (∀ r : Fin 0 → Bool,
    ((γ * B.run G (List.ofFn r) : ℚ≥0) : ℝ) ≤ optimum G) ∧
      α * optimum G ≤
        (∑ r : Fin 0 → Bool, ((γ * B.run G (List.ofFn r) : ℚ≥0) : ℝ)) /
          (Fintype.card (Fin 0 → Bool) : ℝ)
  constructor
  · intro r
    simpa using (h G).1
  · simpa using (h G).2

/-- All remaining assumptions concern the concrete Pauli relaxation
and its one-sided value computation. No approximation algorithm or
unspecified upper-bound function is assumed. -/
theorem exists_algorithm_from_strict_gap
    (α : ℚ≥0) (k : ℕ) (hk : 2 ≤ k) (γ : ℚ≥0)
    (hαγ : (α : ℝ) < (γ : ℝ))
    (hgap : ∀ G : Input,
      (γ : ℝ) * value k G ≤ optimum G ∧ optimum G ≤ value k G)
    (hsolver : ∀ ε : ℚ≥0, 0 < ε →
      ∃ B : Algorithm,
        Nonempty (PolyProgram encodeRequest Ratio.encode
          (fun req : Input × List Bool => (B.run req.1 req.2 : ℚ))) ∧
        B.randomFactor = 0 ∧
        ∀ G : Input,
          (B.run G [] : ℝ) ≤ value k G ∧
          value k G - (ε : ℝ) * (∑ e, (G.weights e : ℝ)) ≤ (B.run G [] : ℝ)) :
    ∃ A : Algorithm, PolynomialTime A ∧ ApproximationRatio A (α : ℝ) := by
  have hαγq : (α : ℚ) < (γ : ℚ) := by exact_mod_cast hαγ
  have hγq : (0 : ℚ) < (γ : ℚ) := lt_of_le_of_lt α.property hαγq
  have hεq : (0 : ℚ) < ((γ : ℚ) - (α : ℚ)) / (4 * (γ : ℚ)) :=
    div_pos (sub_pos.mpr hαγq) (mul_pos (by norm_num) hγq)
  let ε : ℚ≥0 := ⟨((γ : ℚ) - (α : ℚ)) / (4 * (γ : ℚ)), hεq.le⟩
  have hε : 0 < ε := hεq
  obtain ⟨B, ⟨P⟩, hB, hprecision⟩ := hsolver ε hε
  have hεreal : (ε : ℝ) = ((γ : ℝ) - (α : ℝ)) / (4 * (γ : ℝ)) := by
    change (((((γ : ℚ) - (α : ℚ)) / (4 * (γ : ℚ))) : ℚ) : ℝ) = _
    push_cast
    rfl
  have hγreal : (0 : ℝ) < (γ : ℝ) := by exact_mod_cast hγq
  have hproduct : 4 * (γ : ℝ) * (ε : ℝ) = (γ : ℝ) - (α : ℝ) := by
    rw [hεreal]
    field_simp [hγreal.ne']
  have hmargin : (α : ℝ) ≤ (γ : ℝ) * (1 - 2 * (ε : ℝ)) := by nlinarith
  refine ⟨scaledMachine γ B, scaledMachine_polynomialTime γ B P, ?_⟩
  apply scaledMachine_ratio γ B (α : ℝ)
  intro G
  exact QuantumMaxCutEnergy.scaled_bounds G (value k G) (B.run G []) γ
    (α : ℝ) (ε : ℝ) (by exact_mod_cast hε.le)
    (hgap G).2 (hgap G).1 (hprecision G).1 (hprecision G).2 hmargin

#print axioms scaledMachine_polynomialTime
#print axioms scaledMachine_ratio
#print axioms exists_algorithm_from_strict_gap

end QuantumMaxCutEnergy.PauliSDP


theorem solution :
    ∃ A : QuantumMaxCutEnergy.Algorithm,
      QuantumMaxCutEnergy.PolynomialTime A ∧
      QuantumMaxCutEnergy.ApproximationRatio A (0.595 : ℝ) := by
  obtain ⟨γ, hαγ, _hγ1, hgap⟩ :=
    QuantumMaxCutEnergy.PauliSDP.strict_gap_0595
  simpa using QuantumMaxCutEnergy.PauliSDP.exists_algorithm_from_strict_gap
    (0.595 : ℚ≥0) 2 (by norm_num) γ (by simpa using hαγ) hgap
    (fun ε hε => QuantumMaxCutEnergy.PauliSDP.uniform_value_lower_approximation_compiler
      2 (by norm_num) ε hε)

#print axioms solution
