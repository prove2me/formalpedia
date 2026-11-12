-- Prove2me | solution 1 for QEC.Coding.BDL26RandomPerturbation.measurableSet_geometricAvoidance
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-12T00:52:50.666271+00:00
-- url     : https://prove2.me/submissions/84e93454-cfcf-4447-be40-88e90470eeac

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_AvoidanceDensity
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_GoodAssignments
import Theorems.Thm_QEC_Coding_BDL26RandomPerturbation_measurableSet_eventBad
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_measurableSet_avoid
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_measurableSet_localEvent


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26RandomPerturbation
open BDL26FiniteTannerSquare BDL26BoundedValence BDL26ReplacementEmbedding
open QEC.Coding.ProbabilisticConstruction
open QEC.Coding.ProbabilisticConstruction.SphericalCap
open MeasureTheory
namespace QEC.Coding.BDL26RandomPerturbation
theorem _root_.solution (P : TannerSquarePresentation) (J : Vertex P → Space)
    {L : ℝ} (p : GeometricParameters L) : MeasurableSet (geometricAvoidance P J p) := by
  apply measurableSet_avoid
  exact measurableSet_localEvent _ _ (measurableSet_eventBad P J _ _ _)
end QEC.Coding.BDL26RandomPerturbation
