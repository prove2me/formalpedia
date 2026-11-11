-- Prove2me | solution 1 for QEC.Coding.BDL26RandomPerturbation.countedMasterStateEventQuery_original
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T01:09:13.575427+00:00
-- url     : https://prove2.me/submissions/8b545937-bedd-4a57-acf2-1f28f424c3ab

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_JointExecution
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_ActualExecutionCost
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_CountedCostMeasurability

set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26RandomPerturbation
open BDL26FiniteTannerSquare
open QEC.Coding.ProbabilisticConstruction.SphericalCap
open QEC.Coding.ProbabilisticConstruction.Resampling
open MeasureTheory
open scoped ENNReal
attribute [local instance] QEC.Coding.BDL26RandomPerturbation.countedLabelListMeasurable
attribute [local instance] QEC.Coding.BDL26RandomPerturbation.countedLabelListSingleton
namespace QEC.Coding.BDL26RandomPerturbation
theorem _root_.solution (P : TannerSquarePresentation)
    (J : Vertex P → Space) (r lambda : ℝ) (K : ℕ) (e : Event P J r) (R : StateRows P) :
    countedMasterStateEventQuery P J lambda K (eventToMaster P J r e) R =
      stateEventQuery P J r lambda K e R := rfl
end QEC.Coding.BDL26RandomPerturbation
