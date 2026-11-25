-- Prove2me | solution 1 for PI.HookLower.diagHom_monomial
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T09:43:03.349038+00:00
-- url     : https://prove2.me/submissions/28ddd7c3-fffd-4d1c-ab43-cf224bf7cc02

import Definitions.Def_Formalism_PeriodIntegrals_HookBound
import Definitions.Def_Formalism_GradedWeylDivisibility_DualWeylDominanceOf
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HookLengthBound_DiagonalMonomialFactorial
import Theorems.Thm_Formalism_GradedWeylDivisibility_CoeffHom_prod


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial Formalism.GradedWeylDivisibility
noncomputable section
open PI PI.HookLower
open scoped Classical
namespace PI.HookLower
theorem _root_.solution {N : ℕ} (m : Fin N × Fin N →₀ ℕ) (c : ℚ) :
    diagHom N (monomial m c) = if IsDiag m then monomial m c else 0 := by
  classical
  rw [diagHom, aeval_monomial]
  split_ifs with h
  · rw [monomial_eq, algebraMap_eq]
    congr 1
    refine Finsupp.prod_congr fun v hv => ?_
    have : v.1 = v.2 := by
      by_contra hne
      exact (Finsupp.mem_support_iff.1 hv) (h v hne)
    rw [if_pos this]
  · have : ∃ v, v.1 ≠ v.2 ∧ m v ≠ 0 := by
      by_contra hc
      push_neg at hc
      exact h fun v hv => by_contra fun h0 => h0 (hc v hv)
    obtain ⟨v, hv, hmv⟩ := this
    rw [Finsupp.prod, Finset.prod_eq_zero (i := v) (Finsupp.mem_support_iff.2 hmv), mul_zero]
    rw [if_neg hv, zero_pow hmv]
end PI.HookLower
