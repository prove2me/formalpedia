-- Prove2me | solution 1 for QEC.Coding.BDL26RXIncidenceHullGeometry.singleton_escapes
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T13:04:28.372089+00:00
-- url     : https://prove2.me/submissions/85f9a373-7f85-4912-a9f1-ff2fe34005e3

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_QubitBallBounds
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_NativeFiniteComposition
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_RXIncidenceHullRetainedGrowth
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_RXIncidenceHullGeometry
import Theorems.Thm_QEC_Coding_BDL26RXIncidenceHullGeometry_singleton_above_budget
import Theorems.Thm_QEC_Coding_BDL26RXIncidenceHullGeometry_large_mask_escapes

set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26RXIncidenceHullGeometry
open Classical MeasureTheory ProbabilityTheory
open MultiscaleDecoder BDL26IndexedDecoder BDL26FiniteTannerSquare BDL26DecodingGraph
open BDL26RandomPerturbation BDL26RandomPhysicalLocality BDL26QubitBallBounds
open BDL26RXDifferentialMasks BDL26RXIncidenceHullRetainedGrowth
open QEC.Coding.ProbabilisticConstruction.SphericalCap
namespace QEC.Coding.BDL26RXIncidenceHullGeometry
theorem _root_.solution (S : OddScale) {t : ℝ} (R : ℝ)
    (J : Vertex (state S (hullLevel (ballBudget t R))).presentation → Space)
    (geometry : PhysicalGeometry S (hullLevel (ballBudget t R)) J t) (center : Space) :
    ∃ q ∈ incidenceHull S (hullLevel (ballBudget t R)+1) (hullStep (ballBudget t R))
      (seed S (hullLevel (ballBudget t R))), R < dist (J (.q q)) center :=
  large_mask_escapes S _ J geometry R _ (singleton_above_budget S _) center
end QEC.Coding.BDL26RXIncidenceHullGeometry
