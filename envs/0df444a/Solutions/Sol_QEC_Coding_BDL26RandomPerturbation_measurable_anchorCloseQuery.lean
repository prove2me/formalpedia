-- Prove2me | solution 1 for QEC.Coding.BDL26RandomPerturbation.measurable_anchorCloseQuery
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T01:21:19.199209+00:00
-- url     : https://prove2.me/submissions/f84cc3ca-f66a-4756-a816-2c389ae02fe4

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_JointExecution
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_ActualExecutionCost
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_CountedCostMeasurability
import Theorems.Thm_QEC_Coding_BDL26RandomPerturbation_measurable_realTest_run

set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26RandomPerturbation
open BDL26FiniteTannerSquare
open QEC.Coding.ProbabilisticConstruction.SphericalCap
open QEC.Coding.ProbabilisticConstruction.Resampling
open MeasureTheory
open scoped ENNReal
namespace QEC.Coding.BDL26RandomPerturbation
theorem _root_.solution (P : TannerSquarePresentation) (r : ℝ)
    (a b : Triangle P) :
    Measurable (fun J : Vertex P → Space => anchorCloseQuery P J r a b) := by
  apply measurable_realTest_run
  · intro i j
    exact (PiLp.continuous_apply (2 : ℝ≥0∞) (fun _ : Fin 3 => ℝ) j).measurable.comp
      (measurable_pi_apply (Vertex.x (P.faceX b.1) : Vertex P))
  · intro j
    exact (PiLp.continuous_apply (2 : ℝ≥0∞) (fun _ : Fin 3 => ℝ) j).measurable.comp
      (measurable_pi_apply (Vertex.x (P.faceX a.1) : Vertex P))
  · exact measurable_const
end QEC.Coding.BDL26RandomPerturbation
