-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_RestTerms_Top_completeSymmetric_neg_9ceb165058bd
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:40:21.882876+00:00
-- url     : https://prove2.me/submissions/d0518bbf-adaa-400f-9b69-77136cf1435c

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_Expand

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
open GroundTheory.Heights₂.Heights.RestTerms.Top
open MvPolynomial Finset
noncomputable section
namespace GroundTheory.Heights₂.Heights.RestTerms.Top
theorem _root_.solution (σ : Type*) [Fintype σ] [DecidableEq σ] {d : ℤ} (hd : d < 0) :
    completeSymmetric σ d = 0 := by
  simp [completeSymmetric, not_le.mpr hd]
end GroundTheory.Heights₂.Heights.RestTerms.Top
