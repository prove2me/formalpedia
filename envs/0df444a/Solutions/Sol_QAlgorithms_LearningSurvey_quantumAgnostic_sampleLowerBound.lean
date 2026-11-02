-- Prove2me | solution 1 for QAlgorithms.LearningSurvey.quantumAgnostic_sampleLowerBound
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-01T20:44:46.963278+00:00
-- url     : https://prove2.me/submissions/55f4ea02-86ae-4f8a-8cdb-820ca4ea17a3
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_QAlgorithms_Defs_LearningHardInstances
import Theorems.Thm_QAlgorithms_Arunachalam_quantumAgnostic_sample_lower_bound_optimal
set_option autoImplicit false

open MeasureTheory QAlgorithms QAlgorithms.Learning

theorem solution :
    ∃ K : ℝ, 0 < K ∧ ∃ d₀ : ℕ, ∀ (n d : ℕ) (C : Finset (Qubits n → Bool)), d₀ ≤ d →
      vcDimClass C = d →
      ∀ δ ε : ℝ, 0 < δ → δ < 1 / 2 → 0 < ε → ε < 1 / 10 →
      ∀ (T : ℕ) (M : {c // c ∈ C} →
          Matrix (Fin T → Qubits n × Bool) (Fin T → Qubits n × Bool) ℂ),
        IsQAgnosticLearner C ε δ T M →
        K * ((d : ℝ) / ε ^ 2 + (1 / ε ^ 2) * Real.log (1 / δ)) ≤ (T : ℝ) := by
  obtain ⟨C₀, hC₀, d₀, h⟩ := QAlgorithms.Arunachalam.quantumAgnostic_sample_lower_bound_optimal
  refine ⟨C₀, hC₀, d₀, fun n d C hd hvc δ ε hδ0 hδ1 hε0 hε1 T M hL => ?_⟩
  have h1 := h n C d hvc hd δ ε hδ0 hδ1 hε0 hε1 T M hL
  have heq : (1 / ε ^ 2) * Real.log (1 / δ) = Real.log (1 / δ) / ε ^ 2 := by ring
  rw [heq]
  exact h1
