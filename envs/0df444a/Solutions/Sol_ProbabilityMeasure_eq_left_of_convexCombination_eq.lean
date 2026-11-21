-- Prove2me | solution 1 for ProbabilityMeasure.eq_left_of_convexCombination_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-20T21:42:47.169301+00:00
-- url     : https://prove2.me/submissions/b431f5ba-e57f-4ce7-a4df-627b167cbbb4

module
public import Definitions.Def_LeanPool_ChannelCapacity_NonDegeneracy
public import Definitions.Def_LeanPool_ChannelCapacity_KernelCompositionKullbackLeibler
public import Mathlib.Probability.Kernel.Composition.MeasureComp
public import Definitions.Def_LeanPool_ChannelCapacity_StrictConcavity
public import Theorems.Thm_ChannelCapacity_Kernel_priorPushforward_dirac
public import Theorems.Thm_ChannelCapacity_Kernel_priorPushforward_id
public import Theorems.Thm_ChannelCapacity_independentJointLaw_toMeasure
public import Theorems.Thm_ChannelCapacity_jointLaw_toMeasure
public import Theorems.Thm_ChannelCapacity_outputPrior_toMeasure
public import Theorems.Thm_ProbabilityMeasure_convexCombination_apply
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
    (ht_lt_one : t < 1)
    (h : ProbabilityMeasure.convexCombination p q t (le_of_lt ht_lt_one) = p) :
    q = p := by
  apply ProbabilityMeasure.toMeasure_injective
  ext s hs
  have hs_eq : (ProbabilityMeasure.convexCombination p q t (le_of_lt ht_lt_one)).toMeasure s =
      p.toMeasure s := by
    simpa using congrArg (fun μ : ProbabilityMeasure α => μ.toMeasure s) h
  rw [ProbabilityMeasure.convexCombination_apply _ _ _ _ hs] at hs_eq
  have hp_fin : p.toMeasure s ≠ ∞ := measure_ne_top _ _
  have hq_fin : q.toMeasure s ≠ ∞ := measure_ne_top _ _
  have hleft_fin : ((t : ENNReal) * p.toMeasure s) ≠ ∞ := by
    exact ENNReal.mul_ne_top (by simp) hp_fin
  have hright_fin : ((((1 : NNReal) - t : NNReal) : ENNReal) * q.toMeasure s) ≠ ∞ := by
    exact ENNReal.mul_ne_top (by simp) hq_fin
  have hs_real := congrArg ENNReal.toReal hs_eq
  rw [ENNReal.toReal_add hleft_fin hright_fin, ENNReal.toReal_mul, ENNReal.toReal_mul] at hs_real
  have hcoeff : (1 - (t : ENNReal)).toReal = 1 - (t : ℝ) := by
    rw [ENNReal.toReal_sub_of_le]
    · simp
    · exact_mod_cast (le_of_lt ht_lt_one)
    · simp
  have hs_real' :
      (1 - (t : ℝ)) * (q.toMeasure s).toReal = (1 - (t : ℝ)) * (p.toMeasure s).toReal := by
    have hs_real_simp :
        (t : ℝ) * (p.toMeasure s).toReal + (1 - (t : ENNReal)).toReal * (q.toMeasure s).toReal =
          (p.toMeasure s).toReal := by
      simpa using hs_real
    rw [hcoeff] at hs_real_simp
    linarith
  have ht_ne : 1 - (t : ℝ) ≠ 0 := by
    linarith [show (t : ℝ) < 1 by exact_mod_cast ht_lt_one]
  have hs_toReal : (q.toMeasure s).toReal = (p.toMeasure s).toReal := by
    exact mul_left_cancel₀ ht_ne hs_real'
  exact (ENNReal.toReal_eq_toReal_iff' hq_fin hp_fin).mp hs_toReal
end ProbabilityMeasure
