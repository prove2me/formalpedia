-- Prove2me | solution 1 for QEC.Coding.BDL26RandomPerturbation.measurable_listAllQuery
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T23:09:45.738716+00:00
-- url     : https://prove2.me/submissions/c25c86ae-9d3f-4a05-b4c9-a8babb2eba90

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
theorem _root_.solution {Ω A : Type*} [MeasurableSpace Ω]
    (q : A → Ω → Bool × ℕ) (hq : ∀ a, Measurable (q a)) (L : List A) :
    Measurable (fun w => listAllQuery (fun a => q a w) L) := by
  induction L with
  | nil => exact measurable_const
  | cons a L ih =>
      exact (measurable_of_countable (fun t : (Bool × ℕ) × (Bool × ℕ) =>
        (t.1.1 && t.2.1, t.1.2 + t.2.2 + 1))).comp ((hq a).prodMk ih)
end QEC.Coding.BDL26RandomPerturbation
