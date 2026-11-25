-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_RestTerms_FlagEq_ddConst_eq_c1a45b54fd72
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T05:56:43.979922+00:00
-- url     : https://prove2.me/submissions/70132404-90d9-487e-94ea-384c409edea3

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_CoeffRenameProdCongrRight
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_FlagIntegralRealEqMulDdConst
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_FlagEq_ddConst_apply_a09bce188ba1
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_FlagEq_coeff_rho_antisym_e85d46ff9ddc


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
theorem _root_.solution (f j k : ℕ) (G : IndefiniteRowSideFullHecke.RestTerms.Roots f j k) :
    IndefiniteRowSideFullHecke.RestTerms.ddConst f j k G =
      ∑ w, ((permSign f (j + k) w : ℤ) : ℝ) * coeff (stairExp f (j + k) w) G := by
  rw [ddConst_apply, coeff_rho_antisym]
end GroundTheory.Heights₂.Heights.RestTerms.FlagEq
