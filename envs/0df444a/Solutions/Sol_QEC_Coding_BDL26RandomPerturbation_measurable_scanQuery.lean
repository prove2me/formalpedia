-- Prove2me | solution 1 for QEC.Coding.BDL26RandomPerturbation.measurable_scanQuery
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T23:08:10.477705+00:00
-- url     : https://prove2.me/submissions/24ea01f0-b515-4a8b-9bd6-ca0ae7958c78

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
theorem _root_.solution {Ω A : Type*} [MeasurableSpace Ω] [MeasurableSpace A]
    [MeasurableSpace (Option A)]
    (q : A → Ω → Bool × ℕ) (hq : ∀ a, Measurable (q a)) (L : List A) :
    Measurable (scanQuery q L) := by
  induction L with
  | nil => exact measurable_const
  | cons a L ih =>
      have hc : Measurable (fun w => (q a w).2 + 1) :=
        (measurable_of_countable (fun n : ℕ => n + 1)).comp (hq a).snd
      have ht : Measurable (fun w => (q a w).2 + (scanQuery q L w).2 + 1) :=
        (measurable_of_countable (fun t : ℕ × ℕ => t.1 + t.2 + 1)).comp
          ((hq a).snd.prodMk ih.snd)
      exact Measurable.ite (measurableSet_eq_fun (hq a).fst measurable_const)
        (measurable_const.prodMk hc) (ih.fst.prodMk ht)
end QEC.Coding.BDL26RandomPerturbation
