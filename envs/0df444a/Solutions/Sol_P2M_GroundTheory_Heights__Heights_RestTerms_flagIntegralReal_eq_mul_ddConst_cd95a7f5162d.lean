-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_RestTerms_flagIntegralReal_eq_mul_ddConst_cd95a7f5162d
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T10:00:37.636094+00:00
-- url     : https://prove2.me/submissions/595488de-7c86-4b09-ba56-ce1c80d91e12

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_CoeffRenameProdCongrRight
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_FlagIntegralRealEqMulDdConst
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_FlagEq_flagIntegralReal_eq_37604f137363
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_FlagEq_ddConst_eq_c1a45b54fd72

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
open FlagEq
namespace GroundTheory.Heights₂.Heights.RestTerms
theorem _root_.solution (f j k : ℕ) (G : IndefiniteRowSideFullHecke.RestTerms.Roots f j k) :
    flagIntegralReal f (j + k) G = stairConst f (j + k) * IndefiniteRowSideFullHecke.RestTerms.ddConst f j k G := by
  rw [flagIntegralReal_eq, ddConst_eq]
end GroundTheory.Heights₂.Heights.RestTerms
