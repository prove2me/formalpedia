-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_RestTerms_FlagEq_rename_antisym_a583d990c846
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T05:29:30.585298+00:00
-- url     : https://prove2.me/submissions/0e97354f-5264-4d4c-b6e2-9eed33eb5f46

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_CoeffRenameProdCongrRight
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_FlagIntegralRealEqMulDdConst
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_FlagEq_permSign_mul_7d7ff9ee99b1
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_FlagEq_permSign_mul_self_a70738a4eaaa


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
open GroundTheory.Heights₂.Heights.RestTerms.FlagEq
namespace GroundTheory.Heights₂.Heights.RestTerms.FlagEq
theorem _root_.solution (f j k : ℕ) (u : Fin f → Equiv.Perm (Fin (j + k)))
    (G : IndefiniteRowSideFullHecke.RestTerms.Roots f j k) :
    rename (Equiv.prodCongrRight u) (antisym f j k G) =
      ((permSign f (j + k) u : ℤ) : ℝ) • antisym f j k G := by
  have hcomp : ∀ w : Fin f → Equiv.Perm (Fin (j + k)),
      rename (Equiv.prodCongrRight u) (rename (Equiv.prodCongrRight w) G) =
        rename (Equiv.prodCongrRight (u * w)) G := by
    intro w
    rw [rename_rename]
    congr 1
  have hs : ((permSign f (j + k) u : ℤ) : ℝ) * ((permSign f (j + k) u : ℤ) : ℝ) = 1 := by
    exact_mod_cast permSign_mul_self u
  simp only [antisym, map_sum, map_smul, hcomp, smul_sum, smul_smul]
  refine Fintype.sum_equiv (Equiv.mulLeft u) _ _ (fun w => ?_)
  simp only [Equiv.coe_mulLeft, permSign_mul]
  push_cast
  rw [← mul_assoc, hs, one_mul]
end GroundTheory.Heights₂.Heights.RestTerms.FlagEq
