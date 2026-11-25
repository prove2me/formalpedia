-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_RestTerms_Comb_cf_alt_9541255e1ef5
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T04:50:14.063182+00:00
-- url     : https://prove2.me/submissions/bd8943df-e827-4bce-ae75-4d5946cc9ca8

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_Statements
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_VandermondeOfEqDet
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_AltCoeff
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_Comb_alt_eq_sum_69324f4b2849
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_Comb_cf_monomial_c1481e7819e6
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_Comb_cf_sum_377f06929651
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_Comb_cf_zsmul_84a2d79b925d

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.RestTerms GroundTheory.Heights₂.Heights.RestTerms.Comb
open MvPolynomial Finset Equiv
noncomputable section
variable {m : ℕ}
namespace GroundTheory.Heights₂.Heights.RestTerms.Comb
theorem _root_.solution (l v : Fin m → ℕ) :
    cf l (alt v) = ∑ σ : Perm (Fin m), ((Perm.sign σ : ℤ) : ℚ) * if l = v ∘ σ.symm then 1 else 0 := by
  rw [alt_eq_sum, cf_sum]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [cf_zsmul, cf_monomial]
end GroundTheory.Heights₂.Heights.RestTerms.Comb
