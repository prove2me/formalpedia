-- Prove2me | solution 1 for PI.TailWork.small_split
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T10:46:59.213614+00:00
-- url     : https://prove2.me/submissions/c36738fc-3296-4983-9dd9-4b5c2290c743

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PrimeLogarithmTail_SumLogBlock
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PrimeLogarithmTail_SumLogDivSqLeDiv
import Theorems.Thm_PI_TailWork_tail_odd


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PI PI.TailWork
open Finset
namespace PI.TailWork
theorem _root_.solution (a : ℕ) (Q : Finset ℕ) (hQ : ∀ p ∈ Q, p.Prime ∧ a < p) :
    ∑ p ∈ Q, Real.log (p : ℝ) / (p : ℝ) ^ 2
      ≤ ∑ p ∈ ({2, 3, 5} : Finset ℕ).filter (fun p => a < p), Real.log (p : ℝ) / (p : ℝ) ^ 2
        + 2.04 / 7 := by
  classical
  rw [← Finset.sum_filter_add_sum_filter_not Q (fun p => p ∈ ({2, 3, 5} : Finset ℕ))]
  apply add_le_add
  · apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro p hp
      rw [Finset.mem_filter] at hp ⊢
      exact ⟨hp.2, (hQ p hp.1).2⟩
    · intro p _ _
      exact div_nonneg (Real.log_natCast_nonneg p) (by positivity)
  · have h := tail_odd 3 le_rfl
      (Q.filter (fun p => p ∉ ({2, 3, 5} : Finset ℕ))) (by
        intro p hp
        rw [Finset.mem_filter] at hp
        obtain ⟨hpQ, hpT⟩ := hp
        have hpr := (hQ p hpQ).1
        refine ⟨hpr, ?_⟩
        by_contra hlt
        replace hlt : p < 2 * 3 + 1 := not_le.mp hlt
        have h2 := hpr.two_le
        simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hpT
        obtain ⟨n2, n3, n5⟩ := hpT
        interval_cases p
        all_goals first
          | exact (n2 rfl).elim
          | exact (n3 rfl).elim
          | exact (n5 rfl).elim
          | exact absurd hpr (by norm_num))
    norm_num at h ⊢
    linarith
end PI.TailWork
