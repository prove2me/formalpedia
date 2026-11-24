-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_RestTerms_Top_completeSymmetric_zero_8b38a07da8f0
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:42:45.960797+00:00
-- url     : https://prove2.me/submissions/dc5e7fbc-a89c-4afb-b13d-fc779d77ca0e

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
theorem _root_.solution (σ : Type*) [Fintype σ] [DecidableEq σ] :
    completeSymmetric σ 0 = 1 := by
  simp [completeSymmetric, hsymm_zero]
end GroundTheory.Heights₂.Heights.RestTerms.Top
