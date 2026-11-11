-- Prove2me | solution 2 for QuantumMaxCutEnergy.agm_finite_product_estimator
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-01T16:51:22.8562+00:00
-- url     : https://prove2.me/submissions/8f0ef8cb-1e51-42e6-a480-f69cab962a2d

import Definitions.Def_QuantumMaxCutEnergyEstimationModel
import Definitions.Def_QuantumMaxCutFiniteNumericRuntime
import Definitions.Def_ModernConvex_Relaxations_SignRelaxations
import Theorems.Thm_QuantumMaxCutEnergy_agm_classical_sdp_rank_three_gap
import Theorems.Thm_QuantumMaxCutEnergy_agm_classical_sdp_lower_value_program
import Theorems.Thm_QuantumMaxCutEnergy_agm_product_value_scaling
import Theorems.Thm_QuantumMaxCutEnergy_agm_sdp_structural_domination
import Mathlib.Algebra.Order.BigOperators.Group.Finset
open scoped BigOperators

set_option autoImplicit false

open QuantumMaxCutEnergy OAI.MetricKMedian.Binary

/-! ## Elementary facts about a zero-length random tape -/

/-- Summation over the unique Boolean tape of length zero. -/
theorem sum_zero_tape {M : Type} [AddCommMonoid M] (f : (Fin 0 → Bool) → M) :
    (∑ r : Fin 0 → Bool, f r) = f (fun i => i.elim0) := by
  refine Finset.sum_eq_single (fun i : Fin 0 => i.elim0) ?_ ?_
  · intro b _ hb
    exact absurd (funext fun i => i.elim0) hb
  · intro h
    exact absurd (Finset.mem_univ _) h

/-! ## The scaled SDP lower value as a program output -/

def sdpMatrix (G : QuantumMaxCutEnergy.Input) : Matrix (Fin G.n) (Fin G.n) ℝ :=
  Matrix.of fun i j : Fin G.n =>
    if h : i < j then (G.weights ⟨(i, j), h⟩ : ℝ)
    else if h : j < i then (G.weights ⟨(j, i), h⟩ : ℝ) else 0

def weightSum (G : QuantumMaxCutEnergy.Input) : ℝ := ∑ e, (G.weights e : ℝ)

/-- The `0.954`-scaled product estimate attached to a certified lower SDP value `L`. -/
def scaledValue (L : QuantumMaxCutEnergy.Input → ℚ≥0) (G : QuantumMaxCutEnergy.Input) : ℚ≥0 :=
  ((477 : ℚ≥0) / 500) * L G

theorem scaledValue_cast (L : QuantumMaxCutEnergy.Input → ℚ≥0)
    (G : QuantumMaxCutEnergy.Input) : (scaledValue L G : ℝ) = (0.954 : ℝ) * (L G : ℝ) := by
  simp only [scaledValue]
  push_cast
  norm_num

/-- Exact rational scaling of a certified program by the constant `477/500`. -/
noncomputable def scaledValue_program (L : QuantumMaxCutEnergy.Input → ℚ≥0)
    (PL : PolyProgram QuantumMaxCutEnergy.encodeRequest Ratio.encode
      (fun request : QuantumMaxCutEnergy.Input × List Bool => (L request.1 : ℚ))) :
    PolyProgram QuantumMaxCutEnergy.encodeRequest Ratio.encode
      (fun request : QuantumMaxCutEnergy.Input × List Bool => (scaledValue L request.1 : ℚ)) := by
  have hconst : PolyProgram QuantumMaxCutEnergy.encodeRequest Ratio.encode
      (fun _ : QuantumMaxCutEnergy.Input × List Bool => ((477 : ℚ) / 500)) :=
    PolyProgram.constant QuantumMaxCutEnergy.encodeRequest Ratio.encode ((477 : ℚ) / 500)
  have hfan : PolyProgram QuantumMaxCutEnergy.encodeRequest
      (encodePair Ratio.encode Ratio.encode)
      (fun request : QuantumMaxCutEnergy.Input × List Bool =>
        (((477 : ℚ) / 500), (L request.1 : ℚ))) :=
    hconst.fanout PL
  have hmul : PolyProgram QuantumMaxCutEnergy.encodeRequest Ratio.encode
      (fun request : QuantumMaxCutEnergy.Input × List Bool =>
        ((477 : ℚ) / 500) * (L request.1 : ℚ)) :=
    hfan.comp PolyProgram.ratMul
  refine hmul.congr _ (fun request => ?_)
  simp only [scaledValue]
  push_cast
  norm_num

theorem solution :
    ∃ P : QuantumMaxCutEnergy.Algorithm,
      QuantumMaxCutEnergy.PolynomialTime P ∧
      ∀ G : QuantumMaxCutEnergy.Input,
        (∀ r : Fin (QuantumMaxCutEnergy.randomBits P G) → Bool,
          (P.run G (List.ofFn r) : ℝ) ≤ QuantumMaxCutEnergy.optimum G) ∧
        (0.953 : ℝ) * (QuantumMaxCutEnergy.optimum G + (∑ e, (G.weights e : ℝ))) / 3 ≤
          (∑ r : Fin (QuantumMaxCutEnergy.randomBits P G) → Bool,
            (P.run G (List.ofFn r) : ℝ)) /
            (Fintype.card (Fin (QuantumMaxCutEnergy.randomBits P G) → Bool) : ℝ) := by
  classical
  obtain ⟨L, ⟨PL⟩, hL⟩ := QuantumMaxCutEnergy.agm_classical_sdp_lower_value_program
  have hprog : PolyProgram QuantumMaxCutEnergy.encodeRequest
      (fun q : ℚ≥0 => Ratio.encode (q : ℚ))
      (fun request : QuantumMaxCutEnergy.Input × List Bool => scaledValue L request.1) :=
    (scaledValue_program L PL).recode id (fun _ => rfl) (fun _ => rfl)
  refine ⟨⟨0, 0, fun G _ => scaledValue L G⟩,
    ⟨(hprog.comp QMCNumericRuntime.nnratOutput).stock⟩, ?_⟩
  intro G
  obtain ⟨S, hS, hLS, herror⟩ := hL G
  have hstruct : (QuantumMaxCutEnergy.optimum G + weightSum G) / 3 ≤ S :=
    QuantumMaxCutEnergy.agm_sdp_structural_domination G S hS
  have hgap : (0.954 : ℝ) * S ≤ QuantumMaxCutEnergy.optimum G :=
    QuantumMaxCutEnergy.agm_classical_sdp_rank_three_gap G S hS
  have hsl := QuantumMaxCutEnergy.agm_product_value_scaling (QuantumMaxCutEnergy.optimum G)
    (weightSum G) S (L G : ℝ) hstruct hgap (by positivity) hLS herror
  obtain ⟨-, hupper, hlower⟩ := hsl
  have hbits : QuantumMaxCutEnergy.randomBits
      (⟨0, 0, fun G _ => scaledValue L G⟩ : QuantumMaxCutEnergy.Algorithm) G = 0 := by
    simp [QuantumMaxCutEnergy.randomBits]
  have hsum : (∑ r : Fin (QuantumMaxCutEnergy.randomBits
      (⟨0, 0, fun G _ => scaledValue L G⟩ : QuantumMaxCutEnergy.Algorithm) G) → Bool,
        ((⟨0, 0, fun G _ => scaledValue L G⟩ : QuantumMaxCutEnergy.Algorithm).run G
          (List.ofFn r) : ℝ)) =
      (scaledValue L G : ℝ) := by
    rw [hbits, sum_zero_tape]
  have hcard : (Fintype.card (Fin (QuantumMaxCutEnergy.randomBits
      (⟨0, 0, fun G _ => scaledValue L G⟩ : QuantumMaxCutEnergy.Algorithm) G) → Bool) : ℝ) = 1 := by
    rw [hbits]
    simp
  constructor
  · intro r
    change (scaledValue L G : ℝ) ≤ QuantumMaxCutEnergy.optimum G
    rw [scaledValue_cast]
    exact hupper
  · rw [hsum, hcard, div_one, scaledValue_cast]
    have hW : weightSum G = (∑ e, (G.weights e : ℝ)) := rfl
    rw [← hW]
    exact hlower
