-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_RestTerms_Top_yRoot_eq_blockEmb_3d7bdf650708
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T03:53:43.604433+00:00
-- url     : https://prove2.me/submissions/d9c4f254-e879-464c-8f07-f12422baee26

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
theorem _root_.solution (f r a : ℕ) (c : SmallBlock) (σ : Fin f) (i : Fin r) :
    yRoot f r a c σ i = blockEmb f (r + a) σ (yRoot 1 r a c 0 i) := by
  cases c <;> simp [yRoot, yIndex, blockEmb]
end GroundTheory.Heights₂.Heights.RestTerms.Top
