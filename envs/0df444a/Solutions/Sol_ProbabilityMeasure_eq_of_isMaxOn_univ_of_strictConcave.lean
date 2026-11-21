-- Prove2me | solution 1 for ProbabilityMeasure.eq_of_isMaxOn_univ_of_strictConcave
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-20T21:42:46.719557+00:00
-- url     : https://prove2.me/submissions/5060a68d-1b02-4764-8bc4-dde7a10fdc7e

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
theorem _root_.solution
    {f : ProbabilityMeasure α → ℝ}
    (hStrict : ∀ (p q : ProbabilityMeasure α) (_h_ne : p ≠ q) (t : NNReal)
      (_ht_pos : 0 < t) (ht_lt_one : t < 1),
        f (ProbabilityMeasure.convexCombination p q t (le_of_lt ht_lt_one)) >
          (t : ℝ) * f p + (1 - (t : ℝ)) * f q)
    {p q : ProbabilityMeasure α}
    (hp : IsMaxOn f Set.univ p) (hq : IsMaxOn f Set.univ q) : p = q := by
  by_contra hne
  have hp' : ∀ r, f r ≤ f p := isMaxOn_univ_iff.mp hp
  have hq' : ∀ r, f r ≤ f q := isMaxOn_univ_iff.mp hq
  let t : NNReal := 1 / 2
  have ht_pos : 0 < t := by norm_num [t]
  have ht_lt_one : t < 1 := by norm_num [t]
  have hMixLe :
      f (ProbabilityMeasure.convexCombination p q t (le_of_lt ht_lt_one)) ≤ f p :=
    hp' _
  have hpq : f p = f q := le_antisymm (hq' _) (hp' _)
  have hMixGt :
      f (ProbabilityMeasure.convexCombination p q t (le_of_lt ht_lt_one)) >
        (t : ℝ) * f p + (1 - (t : ℝ)) * f q := by
    simpa [t] using hStrict p q hne t ht_pos ht_lt_one
  have hMixGt' :
      f (ProbabilityMeasure.convexCombination p q t (le_of_lt ht_lt_one)) > f p := by
    have hRewrite :
        (t : ℝ) * f p + (1 - (t : ℝ)) * f q = f p := by
      calc
        (t : ℝ) * f p + (1 - (t : ℝ)) * f q =
            (t : ℝ) * f p + (1 - (t : ℝ)) * f p := by simp [hpq]
        _ = ((t : ℝ) + (1 - (t : ℝ))) * f p := by ring
        _ = f p := by ring
    simpa [hRewrite] using hMixGt
  exact (not_lt_of_ge hMixLe) hMixGt'
end ProbabilityMeasure
