-- Prove2me | solution 1 for QuantumMaxCutEnergy.agm_deterministic_product_value_program
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-01T15:07:05.090792+00:00
-- url     : https://prove2.me/submissions/52c8a00e-908b-44c3-abb1-62068c75f0b6
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_QuantumMaxCutEnergy_agm_classical_sdp_rank_three_gap
import Theorems.Thm_QuantumMaxCutEnergy_agm_classical_sdp_lower_value_program
import Theorems.Thm_QuantumMaxCutEnergy_agm_sdp_structural_domination
import Theorems.Thm_QuantumMaxCutEnergy_agm_product_value_scaling

noncomputable section
open scoped BigOperators
open QuantumMaxCutEnergy
open OAI.MetricKMedian.Binary

/-! This sketch has exactly two open analytic/computational child imports.
Its arithmetic and program composition are supplied explicitly below. -/

theorem solution :
    ∃ p : QuantumMaxCutEnergy.Input → ℚ≥0,
      Nonempty (OAI.MetricKMedian.Binary.PolyProgram
        QuantumMaxCutEnergy.encodeRequest OAI.MetricKMedian.Binary.Ratio.encode
        (fun request : QuantumMaxCutEnergy.Input × List Bool => (p request.1 : ℚ))) ∧
      ∀ G : QuantumMaxCutEnergy.Input,
        (p G : ℝ) ≤ QuantumMaxCutEnergy.optimum G ∧
        (0.953 : ℝ) * (QuantumMaxCutEnergy.optimum G + (∑ e, (G.weights e : ℝ))) / 3 ≤
          (p G : ℝ) := by
  obtain ⟨L, ⟨PA⟩, hL⟩ := agm_classical_sdp_lower_value_program
  let p : Input → ℚ≥0 := fun G => L G * (0.954 : ℚ≥0)
  refine ⟨p, ?_, ?_⟩
  · let PC : PolyProgram encodeRequest Ratio.encode
        (fun _ : Input × List Bool => (0.954 : ℚ)) :=
      PolyProgram.constant encodeRequest Ratio.encode (0.954 : ℚ)
    refine ⟨((PA.fanout PC).comp PolyProgram.ratMul).congr _ ?_⟩
    intro request
    simp [p]
  · intro G
    obtain ⟨S, hS, hLS, herror⟩ := hL G
    have hstruct := agm_sdp_structural_domination G S hS
    have hgap := agm_classical_sdp_rank_three_gap G S hS
    have hscaled := agm_product_value_scaling
      (optimum G) (∑ e, (G.weights e : ℝ)) S (L G : ℝ)
      hstruct hgap (by positivity) hLS herror
    have hp : (p G : ℝ) = (0.954 : ℝ) * (L G : ℝ) := by simp [p, mul_comm]
    rw [hp]
    exact ⟨hscaled.2.1, hscaled.2.2⟩

#print axioms solution
