-- Prove2me | solution 1 for ProbabilityMeasure.eq_right_of_convexCombination_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-20T21:43:55.647009+00:00
-- url     : https://prove2.me/submissions/4e9dcacc-7fc4-43b3-a67e-fc912127c72c

module
public import Definitions.Def_LeanPool_ChannelCapacity_NonDegeneracy
public import Definitions.Def_LeanPool_ChannelCapacity_KernelCompositionKullbackLeibler
public import Mathlib.Probability.Kernel.Composition.MeasureComp
public import Definitions.Def_LeanPool_ChannelCapacity_StrictConcavity
public import Theorems.Thm_ProbabilityMeasure_convexCombination_comm
public import Theorems.Thm_ProbabilityMeasure_eq_left_of_convexCombination_eq
public import Theorems.Thm_ChannelCapacity_Kernel_priorPushforward_dirac
public import Theorems.Thm_ChannelCapacity_Kernel_priorPushforward_id
public import Theorems.Thm_ChannelCapacity_independentJointLaw_toMeasure
public import Theorems.Thm_ChannelCapacity_jointLaw_toMeasure
public import Theorems.Thm_ChannelCapacity_outputPrior_toMeasure
public import Theorems.Thm_ProbabilityMeasure_convexCombination_toMeasure
attribute [local simp] ChannelCapacity.Kernel.priorPushforward_dirac
attribute [local simp] ChannelCapacity.Kernel.priorPushforward_id
attribute [local simp] ChannelCapacity.independentJointLaw_toMeasure
attribute [local simp] ChannelCapacity.jointLaw_toMeasure
attribute [local simp] ChannelCapacity.outputPrior_toMeasure
attribute [local simp] ProbabilityMeasure.convexCombination_toMeasure



set_option autoImplicit true
@[expose] public section
public section
open MeasureTheory
open ProbabilityTheory
open scoped BigOperators ENNReal
open ProbabilityMeasure
variable {α : Type*} [MeasurableSpace α]
namespace ProbabilityMeasure
theorem _root_.solution {p q : ProbabilityMeasure α} {t : NNReal}
    (ht_pos : 0 < t) (ht_lt_one : t < 1)
    (h : ProbabilityMeasure.convexCombination p q t (le_of_lt ht_lt_one) = q) :
    p = q := by
  have htsub_lt_one : (1 : NNReal) - t < 1 := by
    simpa using tsub_lt_self (show 0 < (1 : NNReal) by simp) ht_pos
  have hswap :
      ProbabilityMeasure.convexCombination q p (1 - t) (tsub_le_self) = q := by
    calc
      ProbabilityMeasure.convexCombination q p (1 - t) (tsub_le_self) =
          ProbabilityMeasure.convexCombination p q t (le_of_lt ht_lt_one) := by
            simpa using (ProbabilityMeasure.convexCombination_comm p q t (le_of_lt ht_lt_one)).symm
      _ = q := h
  exact eq_left_of_convexCombination_eq (p := q) (q := p) htsub_lt_one hswap
end ProbabilityMeasure
