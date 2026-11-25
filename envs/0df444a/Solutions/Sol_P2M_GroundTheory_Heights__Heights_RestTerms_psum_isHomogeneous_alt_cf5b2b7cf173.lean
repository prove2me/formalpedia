-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_RestTerms_psum_isHomogeneous_alt_cf5b2b7cf173
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T08:25:23.694089+00:00
-- url     : https://prove2.me/submissions/27b9d375-276c-456e-8484-0f7f2933fbcc

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_StatementsSchur
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_PSchPowerSumHomWeighted
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_Comb_IsAlt_sum_a5fe0c99cdcf


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
namespace GroundTheory.Heights₂.Heights.RestTerms
theorem _root_.solution (N j : ℕ) : (psum (Fin N) ℚ j).IsHomogeneous j :=
  IsHomogeneous.sum _ _ _ fun i _ => isHomogeneous_X_pow i j
end GroundTheory.Heights₂.Heights.RestTerms
