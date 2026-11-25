-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_RestTerms_psum_isHomogeneous_89f4e3dcb7ec
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T08:40:30.139516+00:00
-- url     : https://prove2.me/submissions/14a71992-2bf0-4f0d-9e84-328f6f7fa398

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_StatementsSchur
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_AltCoeff
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_PFrobeniusCharacterFormula
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
noncomputable section
namespace GroundTheory.Heights₂.Heights.RestTerms
theorem _root_.solution (σ : Type*) [Fintype σ] (q : ℕ) :
    (psum σ ℚ q).IsHomogeneous q := by
  unfold psum
  exact IsHomogeneous.sum _ _ _ fun i _ => isHomogeneous_X_pow i q
end GroundTheory.Heights₂.Heights.RestTerms
