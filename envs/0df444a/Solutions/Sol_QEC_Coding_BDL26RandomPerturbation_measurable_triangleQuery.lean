-- Prove2me | solution 1 for QEC.Coding.BDL26RandomPerturbation.measurable_triangleQuery
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T01:21:12.839343+00:00
-- url     : https://prove2.me/submissions/18b02ca3-3c43-429c-b296-8f877f719ca1

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
theorem _root_.solution {Ω : Type*} [MeasurableSpace Ω]
    (a : Ω → Fin 3 → Space) (z : Ω → Space) (ρ : Ω → ℝ)
    (ha : ∀ i j, Measurable (fun w => a w i j))
    (hz : ∀ j, Measurable (fun w => z w j)) (hρ : Measurable ρ) :
    Measurable (fun w => triangleQuery (a w) (z w) (ρ w)) :=
  measurable_realTest_run a z ρ ha hz hρ triangleQueryProgram
end QEC.Coding.BDL26RandomPerturbation
