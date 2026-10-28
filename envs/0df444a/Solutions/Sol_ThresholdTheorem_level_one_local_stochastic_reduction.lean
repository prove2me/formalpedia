-- Prove2me | solution 1 for ThresholdTheorem.level_one_local_stochastic_reduction
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-25T20:46:02.823438+00:00
-- url     : https://prove2.me/submissions/22d12340-dcaa-4864-b799-8ef56e3f4db4
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_threshold_theorem_local_stochastic
import Theorems.Thm_ThresholdTheorem_level_one_fault_set_reduction
import Theorems.Thm_ThresholdTheorem_weight_le_of_disjoint_pair_witness

open ThresholdTheorem

theorem solution :
    ∃ (c A : ℝ) (b : ℕ) (dec : (Fin b → Fin 2) → Fin 2), 1 ≤ c ∧
      ∀ (Q : Type) [Fintype Q] [DecidableEq Q] (C : Circuit Q),
        ∃ C' : Circuit (Q × Fin b), (C'.size : ℝ) ≤ A * C.size ∧
          ∀ (e : ℝ), 0 ≤ e → ∀ P : (Q × Fin b → Fin 2) → ℝ, IsLocalStochasticDist C' e P →
            IsLocalStochasticDist C (c * e ^ 2) (pushDist (blockMap dec) P) := by
  obtain ⟨M, A, b, dec, hred⟩ := ThresholdTheorem.level_one_fault_set_reduction
  refine ⟨max (M : ℝ) 1, A, b, dec, le_max_right _ _, ?_⟩
  intro Q _ _ C
  obtain ⟨C', hsize, pairs, Φ, hcard, htwo, hwit, hrep⟩ := hred Q C
  refine ⟨C', hsize, ?_⟩
  intro e he P ⟨r, m, w, F, fault, hw0, hw1, hF, hP⟩
  obtain ⟨m', hm'⟩ := hrep m
  choose fault' hfault' using fun i => hm' (F i) (fault i)
  refine ⟨r, m', w, fun i => Φ (F i), fault', hw0, hw1, ?_, ?_⟩
  · intro S
    refine (weight_le_of_disjoint_pair_witness w F e he hw0 hF M pairs Φ hcard htwo hwit S).trans ?_
    apply pow_le_pow_left₀ (by positivity)
    exact mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)
  · subst hP
    funext y
    simp only [pushDist]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Finset.mul_sum]
    congr 1
    have := congrFun (hfault' i) y
    simpa [pushDist] using this
