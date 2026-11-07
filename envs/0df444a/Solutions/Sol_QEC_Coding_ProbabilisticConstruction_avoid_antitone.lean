-- Prove2me | solution 1 for QEC.Coding.ProbabilisticConstruction.avoid_antitone
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T11:40:59.905086+00:00
-- url     : https://prove2.me/submissions/8ac724b5-8437-4ea5-9cfb-68aed851f237

import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Probability.Independence.Basic
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Tactic
import Definitions.Def_QEC_Coding_ProbabilisticConstruction_LocalLemma

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.ProbabilisticConstruction
open MeasureTheory ProbabilityTheory
open scoped BigOperators
variable {Ω I : Type*} [MeasurableSpace Ω] [Fintype I] [DecidableEq I]
namespace QEC.Coding.ProbabilisticConstruction
theorem _root_.solution (B : I → Set Ω) {S T : Finset I} (h : S ⊆ T) :
    avoid B T ⊆ avoid B S := by
  intro ω hω i hi
  exact hω i (h hi)
end QEC.Coding.ProbabilisticConstruction
