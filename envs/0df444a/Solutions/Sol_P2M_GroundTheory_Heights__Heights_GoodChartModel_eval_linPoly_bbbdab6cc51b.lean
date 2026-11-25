-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_GoodChartModel_eval_linPoly_bbbdab6cc51b
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T14:31:52.597291+00:00
-- url     : https://prove2.me/submissions/e0213f69-4fcd-49fd-b72b-af0addb6f697

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StGoodChartModel
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StGoodChartZeroSet
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StGoodChartDim
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PFiniteProjHomInjective
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PConeAvoidsFinite
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterFib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_PGoodChartModel
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_segre_rel


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
open ReciprocityTheory.ChartRestriction.G.Geo (MRing IsArithVar IsGoodProj mcPts segre segre_rel)
open ComplexSets MvPolynomial Matrix
open GroundTheory.Heights₂.Heights.GoodChartModel
namespace GroundTheory.Heights₂.Heights.GoodChartModel
theorem _root_.solution {n d : ℕ} (A : Matrix (Fin d) (Fin n) ℂ) (r : Fin d) (x : Fin n → ℂ) :
    eval x (linPoly A r) = (A *ᵥ x) r := by
  simp [linPoly, Matrix.mulVec, dotProduct]
end GroundTheory.Heights₂.Heights.GoodChartModel
