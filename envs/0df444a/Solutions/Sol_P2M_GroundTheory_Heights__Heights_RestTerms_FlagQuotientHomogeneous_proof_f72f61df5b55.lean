-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_RestTerms_FlagQuotientHomogeneous_proof_f72f61df5b55
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T19:10:24.768077+00:00
-- url     : https://prove2.me/submissions/d26e7ba3-8c4f-44a8-ab6a-1a0019187046

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_StatementsFlag
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_PHomogeneousComponentMul
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_PFlagQuotientHomogeneous
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_HomogeneousComponentMul_proof_071fefd82e0b


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.RestTerms
open MvPolynomial Finset
noncomputable section
namespace GroundTheory.Heights₂.Heights.RestTerms
namespace FlagQuotientHomogeneous
theorem _root_.solution : FlagQuotientHomogeneous.Statement := by
  intro σ A R m k hA0 hA hAR
  have hzero : ∀ j, j ≠ k → homogeneousComponent j R = 0 := by
    intro j hj
    have h1 := HomogeneousComponentMul.proof σ ℚ A R m (m + j) hA
    rw [if_pos (Nat.le_add_right m j), Nat.add_sub_cancel_left] at h1
    have h2 : homogeneousComponent (m + j) (A * R) = 0 := by
      rw [homogeneousComponent_of_mem ((mem_homogeneousSubmodule _ _).mpr hAR),
        if_neg (by omega)]
    rw [h2] at h1
    exact (mul_eq_zero.mp h1.symm).resolve_left hA0
  have hR : R = homogeneousComponent k R := by
    conv_lhs => rw [← sum_homogeneousComponent R]
    refine Finset.sum_eq_single k (fun j _ hj => hzero j hj) (fun hk => ?_)
    rw [Finset.mem_range, not_lt] at hk
    exact homogeneousComponent_eq_zero k R (by omega)
  rw [hR]
  exact homogeneousComponent_isHomogeneous k R
end FlagQuotientHomogeneous
end GroundTheory.Heights₂.Heights.RestTerms
