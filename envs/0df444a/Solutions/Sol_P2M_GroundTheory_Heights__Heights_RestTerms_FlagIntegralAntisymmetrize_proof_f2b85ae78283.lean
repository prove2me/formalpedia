-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_RestTerms_FlagIntegralAntisymmetrize_proof_f2b85ae78283
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T05:54:06.249511+00:00
-- url     : https://prove2.me/submissions/a98f7eb3-aa1a-4dea-8527-e11e646d5ab5

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_StatementsFlag
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_PFlagIntegralAntisymmetrize
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_flagIntegral_sum_smul_blockPermute_edec349b4023
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_Flag_blockSign_mul_self_a12250e20b18
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_Flag_card_blockPerm_c7329941447d


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
open GroundTheory.Heights₂.Heights.RestTerms
open MvPolynomial Finset
noncomputable section
namespace GroundTheory.Heights₂.Heights.RestTerms
namespace FlagIntegralAntisymmetrize
theorem _root_.solution (h1 : FlagIntegralPermute.Statement) :
    FlagIntegralAntisymmetrize.Statement := by
  intro f N H
  rw [antisymmetrize, flagIntegral_sum_smul_blockPermute]
  rw [Finset.sum_congr rfl fun w _ => by
    rw [h1 f N w H, ← mul_assoc, Flag.blockSign_mul_self, one_mul]]
  rw [Finset.sum_const, Finset.card_univ, Flag.card_blockPerm, nsmul_eq_mul]
  push_cast
  ring
end FlagIntegralAntisymmetrize
end GroundTheory.Heights₂.Heights.RestTerms
