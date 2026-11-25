-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_KRest_sum_card_Ioi_mul_two_69f2c1bd387d
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T04:01:16.513277+00:00
-- url     : https://prove2.me/submissions/f1147b86-8ea9-46d2-88ab-779d67452bdc

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_RestCutBasic
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_KRest_sum_fin_val_mul_two_327ec1f0d7fe

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open GroundTheory.Heights₂.Heights.KRest
open MvPolynomial
noncomputable section
namespace GroundTheory.Heights₂.Heights.KRest
theorem _root_.solution (N : ℕ) :
    (∑ i : Fin N, (Finset.Ioi i).card) * 2 = N * (N - 1) := by
  rw [← sum_fin_val_mul_two N]
  congr 1
  refine Fintype.sum_equiv Fin.revPerm _ _ fun i => ?_
  simp only [Fin.card_Ioi, Fin.revPerm_apply, Fin.val_rev]
  have := i.isLt
  omega
end GroundTheory.Heights₂.Heights.KRest
