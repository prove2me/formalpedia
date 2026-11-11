-- Prove2me | solution 1 for QEC.Coding.BDL26RandomPerturbation.measurable_filterMapQuery
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T23:09:49.109076+00:00
-- url     : https://prove2.me/submissions/db00a76f-81ca-466e-b697-170de0c80a6c

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
theorem _root_.solution {Ω A B : Type*} [MeasurableSpace Ω]
    [Countable B] [MeasurableSpace B] [MeasurableSingletonClass B]
    [MeasurableSpace (Option B)] [MeasurableSingletonClass (Option B)]
    (q : A → Ω → Option B × ℕ) (hq : ∀ a, Measurable (q a)) (L : List A) :
    Measurable (fun w => filterMapQuery (fun a => q a w) L) := by
  induction L with
  | nil => exact measurable_const
  | cons a L ih =>
      exact (measurable_of_countable
        (fun t : (Option B × ℕ) × (List B × ℕ) =>
          ((match t.1.1 with | none => t.2.1 | some b => b :: t.2.1),
            t.1.2 + t.2.2 + 1))).comp ((hq a).prodMk ih)
end QEC.Coding.BDL26RandomPerturbation
