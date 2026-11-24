-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_PtsPosDens_isSmoothHerm_ofWeight_2ba0524d484e
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:00:48.15388+00:00
-- url     : https://prove2.me/submissions/e496b3dc-2f10-4af2-8197-9b04c9e3fd9c

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StPtsPosDensIntegrable
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_PtsSumMeasurableA
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_NoCommonComponentCoordinatesPlane
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_PtsPosDensMeasurable

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
open MvPolynomial MeasureTheory Filter Topology ReciprocityTheory.ChartRestriction.G.Geo InnerProductSpace Laplacian
open GroundTheory.Heights₂.Heights.PtsPosDens
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
namespace GroundTheory.Heights₂.Heights.PtsPosDens
theorem _root_.solution {g : ((Σ k, ι k) → ℂ) → ℝ} (hg : IsDegZeroSmooth g) :
    IsSmoothHerm (HermLine.ofWeight g hg.2) :=
  show ContDiffOn ℝ _ (fun z => Real.exp (-g z)) _ from Real.contDiff_exp.comp_contDiffOn hg.1.neg
end GroundTheory.Heights₂.Heights.PtsPosDens
