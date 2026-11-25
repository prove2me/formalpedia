-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_RestTerms_Top_zRoot_eq_blockEmb_92857d617718
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T05:12:54.814658+00:00
-- url     : https://prove2.me/submissions/719971e5-3715-4d45-a055-8e5ec9869529

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
theorem _root_.solution (f r a : ℕ) (c : SmallBlock) (σ : Fin f) (i : Fin a) :
    zRoot f r a c σ i = blockEmb f (r + a) σ (zRoot 1 r a c 0 i) := by
  cases c <;> simp [zRoot, zIndex, blockEmb]
end GroundTheory.Heights₂.Heights.RestTerms.Top
