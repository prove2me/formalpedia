-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_segre_pblk_injective_89845f6e18bb
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T08:53:18.964883+00:00
-- url     : https://prove2.me/submissions/84f4d286-c3bf-4011-afe3-c3eb32859b60

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsConeSheetParam
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsConeSheetCover
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsConeProjHyperplaneNull
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterBridgeB
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PConeSheetParam
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_segre_pblk_apply_242008ed2609
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_mcPts_smul


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial MeasureTheory Matrix Filter Topology Set
open ReciprocityTheory.ChartRestriction.G.Geo (MRing PBlk IsArithVar IsGoodProj IsSheet fibre segre mcPts
  IsMultiHomogIdeal mcPts_smul)
variable {n : ℕ}
namespace GroundTheory.Heights₂.Heights
theorem _root_.solution : Function.Injective (segre : ((Σ k, PBlk n k) → ℂ) → _) := by
  intro z z' h
  funext p
  obtain ⟨⟨⟩, i⟩ := p
  have := congrFun h fun _ => i
  simpa [segre_pblk_apply] using this
end GroundTheory.Heights₂.Heights
