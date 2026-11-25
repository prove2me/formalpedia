-- Prove2me | solution 1 for P2M_Formalism_CohomologicalDescent_LogSmallConstantBounds_sum_div_mul_log_le_log_factorial__bf9748ec8161
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T00:32:40.703911+00:00
-- url     : https://prove2.me/submissions/a3243ce7-c4f7-4444-af73-5c69f6eed336

import Definitions.Def_Formalism_PieriBlockIdeals_MertensReciprocalElementary
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_SharperSizeNeedsMleKFalse
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_LocalComponentGL
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_LogarithmEquivalence
import Definitions.Def_Formalism_RankGapBounds_RankGapProofs_CardLargePrimeFactorsLeOneHolds
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_ParameterBounds
import Theorems.Thm_Formalism_CohomologicalDescent_LogSmallConstantBounds_log_prime_nonneg

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset
open Formalism Formalism.CohomologicalDescent Formalism.CohomologicalDescent.LogSmallConstantBounds
open Classical
namespace Formalism.CohomologicalDescent.LogSmallConstantBounds
theorem _root_.solution (n : ℕ) :
    ∑ p ∈ Formalism.RankGapBounds.ChebyshevFactorialBounds.primesUpTo n, ((n / p : ℕ) : ℝ) * Real.log (p : ℝ) ≤
      Real.log ((n.factorial : ℕ) : ℝ) := by
  have hfac : n.factorial ≠ 0 := Nat.factorial_ne_zero n
  have hprod := Nat.prod_pow_prime_padicValNat (n.factorial) hfac (n.factorial + 1) (Nat.lt_succ_self _)
  have hlog : Real.log ((n.factorial : ℕ) : ℝ) =
      ∑ p ∈ (Finset.range (n.factorial + 1)).filter Nat.Prime,
        (padicValNat p n.factorial : ℝ) * Real.log (p : ℝ) := by
    have h := congrArg (fun x : ℕ => Real.log (x : ℝ)) hprod
    simp only [Nat.cast_prod, Nat.cast_pow] at h
    rw [Real.log_prod (fun p hp => pow_ne_zero _
      (Nat.cast_ne_zero.2 (Finset.mem_filter.1 hp).2.ne_zero))] at h
    simp only [Real.log_pow] at h
    exact h.symm
  rw [hlog]
  calc ∑ p ∈ Formalism.RankGapBounds.ChebyshevFactorialBounds.primesUpTo n, ((n / p : ℕ) : ℝ) * Real.log (p : ℝ)
      ≤ ∑ p ∈ Formalism.RankGapBounds.ChebyshevFactorialBounds.primesUpTo n, (padicValNat p n.factorial : ℝ) * Real.log (p : ℝ) := by
        apply Finset.sum_le_sum
        intro p hp
        have hp' : p.Prime := (Finset.mem_filter.1 hp).2
        have := Fact.mk hp'
        have hv : n / p ≤ padicValNat p n.factorial := by
          rw [padicValNat_factorial (b := max 2 (Nat.log p n + 1))
            (lt_of_lt_of_le (Nat.lt_succ_self _) (le_max_right _ _))]
          calc n / p = n / p ^ 1 := by rw [pow_one]
            _ ≤ ∑ i ∈ Finset.Ico 1 (max 2 (Nat.log p n + 1)), n / p ^ i :=
                Finset.single_le_sum (f := fun i => n / p ^ i) (fun i _ => Nat.zero_le _)
                  (Finset.mem_Ico.2 ⟨le_rfl, lt_of_lt_of_le (by norm_num) (le_max_left _ _)⟩)
        have hv' : ((n / p : ℕ) : ℝ) ≤ (padicValNat p n.factorial : ℝ) := by exact_mod_cast hv
        exact mul_le_mul_of_nonneg_right hv' (log_prime_nonneg hp')
    _ ≤ ∑ p ∈ (Finset.range (n.factorial + 1)).filter Nat.Prime,
        (padicValNat p n.factorial : ℝ) * Real.log (p : ℝ) := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro p hp
          simp only [Formalism.RankGapBounds.ChebyshevFactorialBounds.primesUpTo, Finset.mem_filter, Finset.mem_range] at hp ⊢
          exact ⟨lt_of_lt_of_le hp.1 (Nat.succ_le_succ (Nat.self_le_factorial n)), hp.2⟩
        · intro p hp _
          have hp' : p.Prime := (Finset.mem_filter.1 hp).2
          exact mul_nonneg (Nat.cast_nonneg _) (log_prime_nonneg hp')
end Formalism.CohomologicalDescent.LogSmallConstantBounds
