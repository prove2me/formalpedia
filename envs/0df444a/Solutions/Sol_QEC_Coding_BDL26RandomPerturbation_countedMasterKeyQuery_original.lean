-- Prove2me | solution 1 for QEC.Coding.BDL26RandomPerturbation.countedMasterKeyQuery_original
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-12T01:10:22.835354+00:00
-- url     : https://prove2.me/submissions/869967f6-5f1e-4a06-b118-dc695455fce7

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
namespace QEC.Coding.BDL26RandomPerturbation
theorem _root_.solution (P : TannerSquarePresentation) (J : Vertex P → Space)
    (r : ℝ) (e : Event P J r) :
    countedMasterKeyQuery P (eventToMaster P J r e) = eventKeyQuery P J r e := rfl
end QEC.Coding.BDL26RandomPerturbation
