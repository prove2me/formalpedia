-- Prove2me | solution 1 for ProbabilityMeasure.convexCombination_comm
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-20T21:42:22.963459+00:00
-- url     : https://prove2.me/submissions/27ef40c0-9741-4b8c-861c-8db32c035894

module
public import Definitions.Def_LeanPool_ChannelCapacity_NonDegeneracy
public import Definitions.Def_LeanPool_ChannelCapacity_KernelCompositionKullbackLeibler
public import Mathlib.Probability.Kernel.Composition.MeasureComp
public import Definitions.Def_LeanPool_ChannelCapacity_StrictConcavity
public import Theorems.Thm_ProbabilityMeasure_convexCombination_apply


set_option autoImplicit true
@[expose] public section
public section
open MeasureTheory
open ProbabilityTheory
open scoped BigOperators ENNReal
open ProbabilityMeasure
variable {α : Type*} [MeasurableSpace α]
namespace ProbabilityMeasure
theorem _root_.solution (p q : ProbabilityMeasure α) (t : NNReal) (ht : t ≤ 1) :
    ProbabilityMeasure.convexCombination p q t ht =
      ProbabilityMeasure.convexCombination q p (1 - t) (tsub_le_self) := by
  apply ProbabilityMeasure.toMeasure_injective
  ext s hs
  rw [ProbabilityMeasure.convexCombination_apply _ _ _ _ hs,
    ProbabilityMeasure.convexCombination_apply _ _ _ _ hs]
  have htsub : ((((1 : NNReal) - ((1 : NNReal) - t) : NNReal) : NNReal) : ENNReal) =
      (t : ENNReal) := by
    exact_mod_cast tsub_tsub_cancel_of_le ht
  rw [htsub, add_comm]
end ProbabilityMeasure
