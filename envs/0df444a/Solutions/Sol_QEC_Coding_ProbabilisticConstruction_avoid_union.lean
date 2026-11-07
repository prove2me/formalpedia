-- Prove2me | solution 1 for QEC.Coding.ProbabilisticConstruction.avoid_union
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T14:51:01.713226+00:00
-- url     : https://prove2.me/submissions/04deaa01-dafb-49dd-a991-c9435ffc9550

import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Probability.Independence.Basic
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Tactic
import Definitions.Def_QEC_Coding_ProbabilisticConstruction_LocalLemma
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_avoid_empty
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_avoid_insert
attribute [local simp] QEC.Coding.ProbabilisticConstruction.avoid_empty
attribute [local simp] QEC.Coding.ProbabilisticConstruction.avoid_insert

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.ProbabilisticConstruction
open MeasureTheory ProbabilityTheory
open scoped BigOperators
variable {Ω I : Type*} [MeasurableSpace Ω] [Fintype I] [DecidableEq I]
namespace QEC.Coding.ProbabilisticConstruction
theorem _root_.solution (B : I → Set Ω) (S T : Finset I) :
    avoid B (S ∪ T) = avoid B S ∩ avoid B T := by
  ext ω
  simp [avoid, or_imp, forall_and]
end QEC.Coding.ProbabilisticConstruction
