-- Prove2me | solution 1 for QEC.Coding.ProbabilisticConstruction.Resampling.measurable_assignment
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T10:18:57.362788+00:00
-- url     : https://prove2.me/submissions/c275caab-cb37-40cb-869b-9a199a7e9e60

import Definitions.Def_QEC_Coding_ProbabilisticConstruction_LocalLemma
import Mathlib.Probability.ProductMeasure
import Mathlib.Data.Finset.Sort
import Definitions.Def_QEC_Coding_ProbabilisticConstruction_Resampling_Execution

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.ProbabilisticConstruction QEC.Coding.ProbabilisticConstruction.Resampling
open MeasureTheory ProbabilityTheory
variable {V I : Type*} [Fintype V] [DecidableEq V] [Fintype I] [LinearOrder I]
variable [MeasurableSpace I] [MeasurableSingletonClass I]
variable {X : V → Type*} [∀ v, MeasurableSpace (X v)]
variable (vars : I → Finset V) (bad : ∀ i, Set (∀ v : vars i, X v))
variable [∀ i, DecidablePred (· ∈ bad i)]
namespace QEC.Coding.ProbabilisticConstruction.Resampling
theorem _root_.solution {c : Table (X := X) → Counters V} (hc : Measurable c) :
    Measurable (fun R => assignment R (c R)) := by
  apply measurable_pi_lambda
  intro v
  have heval : Measurable (fun p : Table (X := X) × ℕ => tableRead p.1 v p.2) := by
    apply measurable_from_prod_countable_left
    intro n
    exact measurable_pi_apply (v, n)
  exact heval.comp (measurable_id.prodMk ((measurable_pi_apply v).comp hc))
end QEC.Coding.ProbabilisticConstruction.Resampling
