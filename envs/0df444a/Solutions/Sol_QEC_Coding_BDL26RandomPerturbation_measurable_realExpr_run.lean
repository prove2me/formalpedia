-- Prove2me | solution 1 for QEC.Coding.BDL26RandomPerturbation.measurable_realExpr_run
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T01:06:15.24125+00:00
-- url     : https://prove2.me/submissions/42e562de-ec0d-4a26-9bab-080c1930f6e0

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_JointExecution
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_ActualExecutionCost
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_CountedCostMeasurability
import Theorems.Thm_QEC_Semantics_QuditSubsystem_ScalarCompression_add

section
noncomputable section
namespace QEC.Coding.BDL26RandomPerturbation
open BDL26FiniteTannerSquare
open QEC.Coding.ProbabilisticConstruction.SphericalCap
open QEC.Coding.ProbabilisticConstruction.Resampling
open MeasureTheory
open scoped ENNReal
private theorem measurable_query_cost {Ω A B : Type*} [MeasurableSpace Ω]
    [MeasurableSpace A] [MeasurableSpace B] {x : Ω → A × ℕ} {y : Ω → B × ℕ}
    (hx : Measurable x) (hy : Measurable y) (c : ℕ) :
    Measurable (fun w => c + (x w).2 + (y w).2) :=
  (measurable_of_countable (fun t : ℕ × ℕ => c + t.1 + t.2)).comp
    (hx.snd.prodMk hy.snd)
end QEC.Coding.BDL26RandomPerturbation
end
end

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
    (hz : ∀ j, Measurable (fun w => z w j)) (hρ : Measurable ρ) (e : RealExpr) :
    Measurable (fun w => e.run (a w) (z w) (ρ w)) := by
  induction e with
  | constant x => exact measurable_const
  | vertex i j => exact (ha i j).prodMk measurable_const
  | center j => exact (hz j).prodMk measurable_const
  | radius => exact hρ.prodMk measurable_const
  | add x y hx hy =>
      exact (hx.fst.add hy.fst).prodMk (measurable_query_cost hx hy 1)
  | sub x y hx hy =>
      exact (hx.fst.sub hy.fst).prodMk (measurable_query_cost hx hy 1)
  | mul x y hx hy =>
      exact (hx.fst.mul hy.fst).prodMk (measurable_query_cost hx hy 1)
  | div x y hx hy =>
      exact Measurable.ite (measurableSet_eq_fun hy.fst measurable_const)
        (measurable_const.prodMk (measurable_query_cost hx hy 1))
        ((hx.fst.div hy.fst).prodMk (measurable_query_cost hx hy 2))
  | min x y hx hy =>
      exact (hx.fst.min hy.fst).prodMk (measurable_query_cost hx hy 1)
  | max x y hx hy =>
      exact (hx.fst.max hy.fst).prodMk (measurable_query_cost hx hy 1)
end QEC.Coding.BDL26RandomPerturbation
