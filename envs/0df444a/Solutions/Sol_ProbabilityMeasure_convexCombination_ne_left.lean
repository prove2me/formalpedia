-- Prove2me | solution 1 for ProbabilityMeasure.convexCombination_ne_left
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-20T21:43:56.187953+00:00
-- url     : https://prove2.me/submissions/7ef74870-561a-4fe1-803d-e6ca6e23b156

module
public import Definitions.Def_LeanPool_ChannelCapacity_NonDegeneracy
public import Definitions.Def_LeanPool_ChannelCapacity_KernelCompositionKullbackLeibler
public import Mathlib.Probability.Kernel.Composition.MeasureComp
public import Definitions.Def_LeanPool_ChannelCapacity_StrictConcavity
public import Theorems.Thm_ProbabilityMeasure_eq_left_of_convexCombination_eq

set_option autoImplicit true
@[expose] public section
public section
open MeasureTheory
open ProbabilityTheory
open scoped BigOperators ENNReal
open ProbabilityMeasure
variable {α : Type*} [MeasurableSpace α]
namespace ProbabilityMeasure
theorem _root_.solution {p q : ProbabilityMeasure α} (h_ne : p ≠ q) {t : NNReal}
    (ht_lt_one : t < 1) :
    ProbabilityMeasure.convexCombination p q t (le_of_lt ht_lt_one) ≠ p := by
  intro h
  exact h_ne ((eq_left_of_convexCombination_eq ht_lt_one h).symm)
end ProbabilityMeasure
