-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ConeProjHyperplaneDim_segre_one_block_dd98c2024510
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T04:10:41.425606+00:00
-- url     : https://prove2.me/submissions/b6c5e0e9-65a1-4635-9844-f0043a041d7a

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsConeProjHyperplaneDim
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PConeSheetParam
import Definitions.Def_GroundTheory_ArithmeticGeometry_ToricVarieties_Dimension
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PConeProjHyperplaneDim

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
open MvPolynomial
open ReciprocityTheory.ChartRestriction.G.Geo (MRing PBlk IsArithVar IsGoodProj segre mcPts psiPoly)
open GroundTheory.Heights₂.Heights.ConeProjHyperplaneDim
namespace GroundTheory.Heights₂.Heights.ConeProjHyperplaneDim
theorem _root_.solution {n : ℕ} (x : Fin n → ℂ) :
    segre (fun p : Σ k, PBlk n k => x p.2) = fun f => x (f ()) := by
  funext f
  simp [segre]
end GroundTheory.Heights₂.Heights.ConeProjHyperplaneDim
