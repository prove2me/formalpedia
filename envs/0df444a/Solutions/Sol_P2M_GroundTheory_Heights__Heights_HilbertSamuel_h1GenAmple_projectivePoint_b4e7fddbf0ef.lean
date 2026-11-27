-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_HilbertSamuel_h1GenAmple_projectivePoint_b4e7fddbf0ef
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-27T04:58:02.171851+00:00
-- url     : https://prove2.me/submissions/f2a8d8da-3aba-4b67-b287-ae88fae67873

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_StatementsKleimanScheme
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_GeneratedModOfSubsingleton
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_HilbertSamuel_h1GenAmple_of_subsingleton_920f91cfcb7d

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.HilbertSamuel
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
noncomputable section
namespace GroundTheory.Heights₂.Heights.HilbertSamuel
theorem _root_.solution : H1GenAmple ℚ (⊥ : Ideal (MRingOver ℚ pointIdx)) 0 :=
  h1GenAmple_of_subsingleton _ _
end GroundTheory.Heights₂.Heights.HilbertSamuel
