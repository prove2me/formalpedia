-- Prove2me | solution 1 for OAI.WeakHessian.every_geodesic
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-27T19:09:34.450295+00:00
-- url     : https://prove2.me/submissions/aa884fdd-2634-4d0e-b727-143979f6c4c9

import Mathlib
import Definitions.Def_WeakHessian
import Definitions.Def_OAIQ52Wh007
import Theorems.Thm_OAI_WeakHessian_RCD_weighted_heat_concentration
import Theorems.Thm_OAI_WeakHessian_WeakHessianUpperBound_rcd_localized_plan_law

section
-- module Solutions.OAIQ52_WH.WeakHessian_Calculus_ScalarSecondDifference
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section
open Set Filter MeasureTheory
open scoped Topology

noncomputable section
attribute [local instance] Classical.propDecidable
namespace WeakHessian

lemma taylorPolynomial_two {f : ℝ → ℝ} (x y : ℝ) :
    taylorWithinEval f 2 univ x y =
      f x + (y - x) * deriv f x + (y - x) ^ 2 / 2 * deriv (deriv f) x := by
  norm_num only [taylorWithinEval_succ, taylor_within_zero_eval,
    iteratedDerivWithin_univ, iteratedDeriv_succ, iteratedDeriv_zero,
    smul_eq_mul, Nat.factorial]
  ring

lemma secondDifference_tendsto {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f) (x : ℝ) :
    Tendsto (fun h => secondDifference f h x) (𝓝[≠] 0) (𝓝 (deriv (deriv f) x)) := by
  have ht : Tendsto
      (fun y => (f y - (f x + (y - x) * deriv f x +
        (y - x) ^ 2 / 2 * deriv (deriv f) x)) / (y - x) ^ 2)
      (𝓝 x) (𝓝 0) := by
    simpa only [nhdsWithin_univ, taylorPolynomial_two, smul_eq_mul, div_eq_inv_mul] using
      (Real.taylor_tendsto convex_univ (mem_univ x) hf.contDiffOn)
  have hap : Tendsto (fun h : ℝ => x + h) (𝓝[≠] 0) (𝓝 x) := by
    simpa using (tendsto_const_nhds.add
      (tendsto_id.mono_left nhdsWithin_le_nhds) :
        Tendsto (fun h : ℝ => x + h) (𝓝[≠] 0) (𝓝 (x + 0)))
  have ham : Tendsto (fun h : ℝ => x - h) (𝓝[≠] 0) (𝓝 x) := by
    simpa using (tendsto_const_nhds.sub
      (tendsto_id.mono_left nhdsWithin_le_nhds) :
        Tendsto (fun h : ℝ => x - h) (𝓝[≠] 0) (𝓝 (x - 0)))
  have hp := ht.comp hap
  have hm := ht.comp ham
  have hc := (hp.add hm).add_const (deriv (deriv f) x)
  simp only [zero_add] at hc
  apply hc.congr'
  filter_upwards [self_mem_nhdsWithin] with h hh
  have hn : h ≠ 0 := hh
  dsimp only [Function.comp_def, secondDifference]
  field_simp [hn]
  ring

lemma taylor_remainder_one {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f) {x y : ℝ}
    (hxy : x ≠ y) :
    ∃ z ∈ uIoo x y, f y - (f x + (y - x) * deriv f x) =
      deriv (deriv f) z * (y - x) ^ 2 / 2 := by
  obtain ⟨z, hz, he⟩ := taylor_mean_remainder_lagrange_iteratedDeriv
    (n := 1) hxy hf.contDiffOn
  refine ⟨z, hz, ?_⟩
  have hd : derivWithin f (uIcc x y) x = deriv f x :=
    (hf.differentiable (by norm_num) x).hasDerivAt.hasDerivWithinAt.derivWithin
      (uniqueDiffOn_uIcc hxy x left_mem_uIcc)
  simpa [taylorWithinEval_succ, iteratedDerivWithin_one, hd,
    iteratedDeriv_succ, smul_eq_mul] using he

lemma norm_secondDifference_le {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f) {M : ℝ}
    (hM : 0 ≤ M) (hbound : ∀ x, |deriv (deriv f) x| ≤ M) (h x : ℝ) :
    |secondDifference f h x| ≤ M := by
  by_cases hh : h = 0
  · simp [secondDifference, hh, hM]
  have hp : x ≠ x + h := by intro he; apply hh; linarith
  have hm : x ≠ x - h := by intro he; apply hh; linarith
  obtain ⟨z, _, hz⟩ := taylor_remainder_one hf hp
  obtain ⟨w, _, hw⟩ := taylor_remainder_one hf hm
  have he : secondDifference f h x = (deriv (deriv f) z + deriv (deriv f) w) / 2 := by
    simp only [secondDifference]
    apply (div_eq_iff (pow_ne_zero 2 hh)).2
    simp only [add_sub_cancel_left, sub_sub_cancel_left, neg_sq] at hz hw
    nlinarith
  rw [he, abs_div, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
  have := (abs_add_le (deriv (deriv f) z) (deriv (deriv f) w)).trans
    (add_le_add (hbound z) (hbound w))
  linarith

lemma integral_mul_translate (f φ : ℝ → ℝ) (h : ℝ) :
    (∫ x, f x * φ (x + h)) = ∫ x, f (x - h) * φ x := by
  simpa only [add_sub_cancel_right] using
    integral_add_right_eq_self (fun x => f (x - h) * φ x) h

lemma integrable_mul_translate {f φ : ℝ → ℝ} (hf : Continuous f)
    (hφ : Continuous φ) (hc : HasCompactSupport φ) (h : ℝ) :
    Integrable (fun x => f x * φ (x + h)) := by
  apply (hf.mul (hφ.comp (continuous_id.add continuous_const))).integrable_of_hasCompactSupport
  exact (hc.comp_homeomorph (Homeomorph.addRight h)).mul_left

lemma integrable_translate_mul {f φ : ℝ → ℝ} (hf : Continuous f)
    (hφ : Continuous φ) (hc : HasCompactSupport φ) (h : ℝ) :
    Integrable (fun x => f (x + h) * φ x) := by
  apply ((hf.comp (continuous_id.add continuous_const)).mul hφ).integrable_of_hasCompactSupport
  exact hc.mul_left

lemma integral_mul_secondDifference {f φ : ℝ → ℝ} (hf : Continuous f)
    (hφ : Continuous φ) (hc : HasCompactSupport φ) (h : ℝ) :
    (∫ x, f x * secondDifference φ h x) = ∫ x, secondDifference f h x * φ x := by
  have hi := integrable_mul_translate hf hφ hc h
  have hj : Integrable (fun x => f x * φ (x - h)) := by
    simpa only [sub_eq_add_neg] using integrable_mul_translate hf hφ hc (-h)
  have hk : Integrable (fun x => f x * φ x) := by
    simpa only [add_zero] using integrable_mul_translate hf hφ hc 0
  have Hil := integrable_translate_mul hf hφ hc h
  have Hjl : Integrable (fun x => f (x - h) * φ x) := by
    simpa only [sub_eq_add_neg] using integrable_translate_mul hf hφ hc (-h)
  have e₁ := integral_mul_translate f φ h
  have e₂ : (∫ x, f x * φ (x - h)) = ∫ x, f (x + h) * φ x := by
    simpa only [sub_neg_eq_add, ← sub_eq_add_neg] using integral_mul_translate f φ (-h)
  have ea : (fun x => f x * secondDifference φ h x) =
      (fun x => (f x * φ (x + h) + f x * φ (x - h) - 2 * (f x * φ x)) / h ^ 2) := by
    funext x
    dsimp [secondDifference]
    ring
  have eb : (fun x => secondDifference f h x * φ x) =
      (fun x => (f (x + h) * φ x + f (x - h) * φ x - 2 * (f x * φ x)) / h ^ 2) := by
    funext x
    dsimp [secondDifference]
    ring
  have hia : Integrable (fun x => f x * φ (x + h) + f x * φ (x - h)) := hi.add hj
  have hib : Integrable (fun x => f (x + h) * φ x + f (x - h) * φ x) := Hil.add Hjl
  rw [ea, eb, integral_div, integral_div, integral_sub hia (hk.const_mul 2),
    integral_add hi hj, integral_sub hib (hk.const_mul 2),
    integral_add Hil Hjl, e₁, e₂, add_comm]

lemma secondDifference_eq_zero_outside {φ : ℝ → ℝ}
    (hs : tsupport φ ⊆ Ioo (0 : ℝ) 1) {h x : ℝ} (hh : |h| < 1)
    (hx : x ∉ Icc (-1 : ℝ) 2) : secondDifference φ h x = 0 := by
  have he {y : ℝ} (hy : y ∉ Ioo (0 : ℝ) 1) : φ y = 0 :=
    image_eq_zero_of_notMem_tsupport (fun hp => hy (hs hp))
  have hh' := abs_lt.mp hh
  have hp : φ (x + h) = 0 := by
    apply he
    intro hy
    apply hx
    constructor <;> linarith [hy.1, hy.2]
  have hm : φ (x - h) = 0 := by
    apply he
    intro hy
    apply hx
    constructor <;> linarith [hy.1, hy.2]
  have hz : φ x = 0 := by
    apply he
    intro hy
    apply hx
    constructor <;> linarith [hy.1, hy.2]
  simp only [secondDifference, hp, hm, hz, mul_zero, add_zero, sub_zero, zero_div]

lemma integral_secondDifference_tendsto {f φ : ℝ → ℝ} (hf : Continuous f)
    (hφ : ContDiff ℝ 2 φ) (hc : HasCompactSupport φ)
    (hs : tsupport φ ⊆ Ioo (0 : ℝ) 1) :
    Tendsto (fun h => ∫ x, f x * secondDifference φ h x) (𝓝[≠] 0)
      (𝓝 (∫ x, f x * deriv (deriv φ) x)) := by
  have hdφ : ContDiff ℝ 1 (deriv φ) := hφ.deriv'
  have hddφ := hdφ.continuous_deriv_one
  obtain ⟨M, hM⟩ := hddφ.bounded_above_of_compact_support hc.deriv.deriv
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0)
  obtain ⟨B, hB⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (hf.continuousOn : ContinuousOn f (Icc (-1 : ℝ) 2))
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB 0 (by norm_num))
  have hcF (h : ℝ) : Continuous (fun x => f x * secondDifference φ h x) := by
    dsimp only [secondDifference]
    have := hφ.continuous
    fun_prop
  have hlim := tendsto_integral_filter_of_dominated_convergence
    (μ := volume.restrict (Icc (-1 : ℝ) 2)) (l := 𝓝[≠] (0 : ℝ))
    (fun _ => B * M)
    (Eventually.of_forall fun h => (hcF h).aestronglyMeasurable)
    (Eventually.of_forall fun h => ?_)
    (integrable_const (B * M))
    (Eventually.of_forall fun x => tendsto_const_nhds.mul (secondDifference_tendsto hφ x))
  · have he : (∫ x in Icc (-1 : ℝ) 2, f x * deriv (deriv φ) x) =
        ∫ x, f x * deriv (deriv φ) x := by
      apply setIntegral_eq_integral_of_forall_compl_eq_zero
      intro x hx
      have hn : x ∉ tsupport (deriv (deriv φ)) := by
        intro hp
        have hp' := hs (tsupport_deriv_subset (tsupport_deriv_subset hp))
        exact hx ⟨by linarith [hp'.1], by linarith [hp'.2]⟩
      rw [image_eq_zero_of_notMem_tsupport hn, mul_zero]
    rw [he] at hlim
    apply hlim.congr'
    have hev : ∀ᶠ h : ℝ in 𝓝[≠] 0, |h| < 1 := by
      simpa only [sub_zero] using (eventually_abs_sub_lt (0 : ℝ) zero_lt_one).filter_mono
        nhdsWithin_le_nhds
    filter_upwards [hev] with h hh
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro x hx
    rw [secondDifference_eq_zero_outside hs hh hx, mul_zero]
  · filter_upwards [ae_restrict_mem measurableSet_Icc] with x hx
    rw [norm_mul, Real.norm_eq_abs (secondDifference φ h x)]
    apply mul_le_mul (hB x hx) (norm_secondDifference_le hφ hM0 (by simpa using hM) h x)
      (abs_nonneg _) hB0

end WeakHessian

end
end

end OAI
end

section
-- module Solutions.OAIQ52_WH.WeakHessian_Calculus_ScalarLocalBound
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section
noncomputable section
namespace WeakHessian
open Set Filter MeasureTheory
open scoped Topology

lemma integral_second_deriv_le_of_local_differences {f q φ : ℝ → ℝ}
    (hf : Continuous f) (hq : Continuous q)
    (hlocal : ∀ ε : ℝ,0 < ε → ∃ δ : ℝ,0 < δ ∧ ∀ h : ℝ,0 < h → h < δ →
      ∀ x : ℝ,x-h ∈ Ioo (0:ℝ) 1 → x+h ∈ Ioo (0:ℝ) 1 → secondDifference f h x ≤ q x+ε)
    (hφ : ContDiff ℝ 2 φ) (hc : HasCompactSupport φ)
    (hs : tsupport φ ⊆ Ioo (0:ℝ) 1) (hnn : ∀ x,0 ≤ φ x) :
    (∫ x,f x*deriv (deriv φ) x) ≤ ∫ x,q x*φ x := by
  have H (ε : ℝ) (hε : 0 < ε) :
      (∫ x,f x*deriv (deriv φ) x) ≤ (∫ x,q x*φ x)+ε*(∫ x,φ x) := by
    obtain ⟨δ,hδ,hbound⟩ := hlocal ε hε
    obtain ⟨η,hη,hηs⟩ := hc.exists_thickening_subset_open isOpen_Ioo hs
    have hi : Integrable (fun x => q x*φ x) := (hq.mul hφ.continuous).integrable_of_hasCompactSupport hc.mul_left
    have hj : Integrable φ := hφ.continuous.integrable_of_hasCompactSupport hc
    have he : (∫ x,(q x+ε)*φ x) = (∫ x,q x*φ x)+ε*(∫ x,φ x) := by
      simp_rw [add_mul]
      rw [integral_add hi (hj.const_mul ε),integral_const_mul]
    rw [← he]
    apply le_of_tendsto_of_tendsto
      ((integral_secondDifference_tendsto hf hφ hc hs).mono_left (nhdsGT_le_nhdsNE 0)) tendsto_const_nhds
    have hsmall : ∀ᶠ h : ℝ in 𝓝[>] 0,|h| < η ∧ h < δ := by
      filter_upwards [(eventually_abs_sub_lt (0:ℝ) hη).filter_mono nhdsWithin_le_nhds,
        (eventually_lt_nhds hδ).filter_mono nhdsWithin_le_nhds] with h hh hh'
      exact ⟨by simpa only [sub_zero] using hh,hh'⟩
    filter_upwards [hsmall,self_mem_nhdsWithin] with h hh (hhpos : 0 < h)
    rw [integral_mul_secondDifference hf hφ.continuous hc]
    have hdf : Continuous (fun x => secondDifference f h x) := by
      dsimp only [secondDifference]
      fun_prop
    apply integral_mono
      ((hdf.mul hφ.continuous).integrable_of_hasCompactSupport hc.mul_left)
      (((hq.add continuous_const).mul hφ.continuous).integrable_of_hasCompactSupport hc.mul_left)
    intro x
    change secondDifference f h x*φ x ≤ (q x+ε)*φ x
    by_cases hx : φ x = 0
    · simp only [hx,mul_zero,le_refl]
    have hxs : x ∈ tsupport φ := subset_closure hx
    have hp : x+h ∈ Ioo (0:ℝ) 1 := by
      apply hηs
      apply Metric.mem_thickening_iff.mpr
      exact ⟨x,hxs,by simpa only [Real.dist_eq,add_sub_cancel_left] using hh.1⟩
    have hm : x-h ∈ Ioo (0:ℝ) 1 := by
      apply hηs
      apply Metric.mem_thickening_iff.mpr
      exact ⟨x,hxs,by simpa only [Real.dist_eq,sub_sub_cancel_left,abs_neg] using hh.1⟩
    exact mul_le_mul_of_nonneg_right (hbound h hhpos hh.2 x hm hp) (hnn x)
  have hlim : Tendsto (fun ε : ℝ => (∫ x,q x*φ x)+ε*(∫ x,φ x)) (𝓝[>] 0) (𝓝 (∫ x,q x*φ x)) := by
    convert (show ContinuousAt (fun ε : ℝ => (∫ x,q x*φ x)+ε*(∫ x,φ x)) 0 from by fun_prop).tendsto.mono_left nhdsWithin_le_nhds using 1
    all_goals try with_reducible_and_instances rfl
    simp
  apply ge_of_tendsto hlim
  filter_upwards [self_mem_nhdsWithin] with ε hε
  exact H ε hε

lemma setIntegral_second_deriv_le_of_local_differences {f q φ : ℝ → ℝ}
    (hf : Continuous f) (hq : Continuous q)
    (hlocal : ∀ ε : ℝ,0 < ε → ∃ δ : ℝ,0 < δ ∧ ∀ h : ℝ,0 < h → h < δ →
      ∀ x : ℝ,x-h ∈ Ioo (0:ℝ) 1 → x+h ∈ Ioo (0:ℝ) 1 → secondDifference f h x ≤ q x+ε)
    (hφ : ContDiff ℝ 2 φ) (hc : HasCompactSupport φ)
    (hs : tsupport φ ⊆ Ioo (0:ℝ) 1) (hnn : ∀ x,0 ≤ φ x) :
    (∫ x in Icc (0:ℝ) 1,f x*deriv (deriv φ) x) ≤ ∫ x in Icc (0:ℝ) 1,q x*φ x := by
  have he₁ : (∫ x in Icc (0:ℝ) 1,f x*deriv (deriv φ) x) = ∫ x,f x*deriv (deriv φ) x := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro x hx
    have hn : x ∉ tsupport (deriv (deriv φ)) := by
      intro hp
      have hxp := hs (tsupport_deriv_subset (tsupport_deriv_subset hp))
      exact hx ⟨hxp.1.le,hxp.2.le⟩
    rw [image_eq_zero_of_notMem_tsupport hn,mul_zero]
  have he₂ : (∫ x in Icc (0:ℝ) 1,q x*φ x) = ∫ x,q x*φ x := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro x hx
    have hn : x ∉ tsupport φ := fun hp => hx ⟨(hs hp).1.le,(hs hp).2.le⟩
    rw [image_eq_zero_of_notMem_tsupport hn,mul_zero]
  rw [he₁,he₂]
  exact integral_second_deriv_le_of_local_differences hf hq hlocal hφ hc hs hnn
end WeakHessian

end
end

end OAI
end

section
-- module Solutions.OAIQ52_WH.WeakHessian_Geodesics_TwoLegLimit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section
noncomputable section
namespace WeakHessian
open Set Filter
open scoped Topology

lemma le_at_zero_of_positive {f g : ℝ → ℝ} (hf : ContinuousAt f 0)
    (hg : ContinuousAt g 0) (h : ∀ t,0 < t → f t ≤ g t) : f 0 ≤ g 0 := by
  exact le_of_tendsto_of_tendsto (hf.tendsto.mono_left nhdsWithin_le_nhds)
    (hg.tendsto.mono_left nhdsWithin_le_nhds)
    (eventually_nhdsWithin_of_forall fun t (ht : t ∈ Ioi (0:ℝ)) => h t ht)

end WeakHessian

end
end

end OAI
end

section
-- module Solutions.OAIQ52_WH.WeakHessian_LocalBounds_Smul
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile0
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

noncomputable section
open scoped ENNReal NNReal Topology BoundedContinuousFunction CompactlySupported
open scoped ENNReal NNReal Topology BoundedContinuousFunction
open scoped NNReal
open MeasureTheory Set Filter
open scoped Topology NNReal ENNReal
open scoped ENNReal NNReal Topology InnerProductSpace
open Set Filter Bornology
open MeasureTheory
open scoped ENNReal InnerProductSpace ComplexConjugate
open Set Filter
open scoped Topology ENNReal NNReal
open Set
open Set MeasureTheory CompactlySupported CompactlySupportedContinuousMap
open scoped Topology ENNReal NNReal InnerProductSpace
open scoped BoundedContinuousFunction
open Set MeasureTheory Filter
open Set Filter MeasureTheory Topology TopologicalSpace
open scoped ENNReal NNReal
open Set MeasureTheory ProbabilityTheory
open scoped ENNReal MeasureTheory ProbabilityTheory
open Set Filter Topology Bornology
open scoped InnerProductSpace
open Filter
open scoped Topology

attribute [local instance] Classical.propDecidable
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

namespace WeakHessian
open MeasureTheory Filter
open scoped Topology

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
variable [CompleteSpace X] [TopologicalSpace.SeparableSpace X] {m ν : Measure X}

omit [BorelSpace X] [CompleteSpace X] [TopologicalSpace.SeparableSpace X] in
lemma FiniteOnBoundedSets.of_le_smul (hfinite : FiniteOnBoundedSets m) {C : ℝ≥0}
    (hν : ν ≤ (C:ℝ≥0∞) • m) : FiniteOnBoundedSets ν := by
  intro s hs
  have H : (C:ℝ≥0∞)*m s < ∞ := ENNReal.mul_lt_top ENNReal.coe_lt_top (hfinite s hs)
  exact lt_of_le_of_lt (hν s) (by simpa only [Measure.smul_apply,smul_eq_mul] using H)

end WeakHessian

end
end InlinedFile0

end OAI
end

section
-- module Solutions.OAIQ52_WH.WeakHessian_Sobolev_UpperGradientTendstoNorm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

noncomputable section
open scoped ENNReal NNReal Topology BoundedContinuousFunction CompactlySupported
open scoped ENNReal NNReal Topology BoundedContinuousFunction
open MeasureTheory
open scoped ENNReal InnerProductSpace ComplexConjugate
open scoped Topology ENNReal NNReal
open Set MeasureTheory CompactlySupported CompactlySupportedContinuousMap
open scoped Topology ENNReal NNReal InnerProductSpace
open scoped BoundedContinuousFunction
open Set MeasureTheory Filter
open Set Filter MeasureTheory Topology TopologicalSpace
open scoped ENNReal NNReal
open Set MeasureTheory ProbabilityTheory
open scoped ENNReal MeasureTheory ProbabilityTheory
open Set
open scoped NNReal
open Set Filter
open scoped ENNReal NNReal Topology InnerProductSpace
open Set Filter Bornology
open scoped Topology
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

attribute [local instance] Classical.propDecidable
open Set Filter Topology Bornology
open scoped InnerProductSpace

namespace WeakHessian

section NormConvergence
open MeasureTheory Filter
open scoped Topology InnerProductSpace

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
variable {m : Measure X}

lemma upperGradient_tendsto_of_norm_tendsto {fn Dn : ℕ → Lp ℝ 2 m} {f D : Lp ℝ 2 m}
    (hn : ∀ n, IsLocalWeakUpperGradient m (fn n) (Dn n))
    (hf : Tendsto fn atTop (𝓝 f)) (hD : IsLocalWeakUpperGradient m f D)
    (hmin : ∀ E : Lp ℝ 2 m, IsLocalWeakUpperGradient m f E → ‖D‖ ≤ ‖E‖)
    (hNorm : Tendsto (fun n => ‖Dn n‖) atTop (𝓝 ‖D‖)) :
    Tendsto Dn atTop (𝓝 D) := by
  let fm : ℕ → Lp ℝ 2 m := fun n => (1/2 : ℝ) • fn n + (1/2 : ℝ) • f
  let Dm : ℕ → Lp ℝ 2 m := fun n => (1/2 : ℝ) • Dn n + (1/2 : ℝ) • D
  have hmid (n : ℕ) : IsLocalWeakUpperGradient m (fm n) (Dm n) := by
    exact convex_l2GradientGraph (m := m)
      (x := WithLp.toLp 2 (fn n, Dn n)) (y := WithLp.toLp 2 (f,D))
      (hn n) hD (by norm_num) (by norm_num) (by norm_num)
  have hfm : Tendsto fm atTop (𝓝 f) := by
    have H := (hf.const_smul (1/2 : ℝ)).add
      (tendsto_const_nhds (x := (1/2 : ℝ) • f))
    simpa only [← add_smul, show (1/2:ℝ)+(1/2)=1 by norm_num, one_smul] using H
  have hlow (a : ℝ) (ha : a < ‖D‖) : ∀ᶠ n in atTop, a < ‖Dm n‖ := by
    have hout : f ∈ {u : Lp ℝ 2 m | ∃ E : Lp ℝ 2 m,
        IsLocalWeakUpperGradient m u E ∧ ‖E‖ ≤ a}ᶜ := by
      rintro ⟨E,hE,he⟩
      exact (not_le_of_gt ha) ((hmin E hE).trans he)
    have H := hfm.eventually ((isClosed_upperGradient_sublevel (m := m) a).isOpen_compl.mem_nhds hout)
    filter_upwards [H] with n hn'
    exact lt_of_not_ge (fun hle => hn' ⟨Dm n,hmid n,hle⟩)
  have hupper (n : ℕ) : ‖Dm n‖ ≤ (‖Dn n‖+‖D‖)/2 := by
    calc
      ‖Dm n‖ ≤ ‖(1/2 : ℝ) • Dn n‖ + ‖(1/2 : ℝ) • D‖ := norm_add_le _ _
      _ = (‖Dn n‖+‖D‖)/2 := by
        rw [norm_smul, norm_smul, Real.norm_of_nonneg (by norm_num : (0 : ℝ) ≤ 1/2)]
        ring
  have hmajor : Tendsto (fun n => (‖Dn n‖+‖D‖)/2) atTop (𝓝 ‖D‖) := by
    convert (hNorm.add_const ‖D‖).div_const 2 using 1
    all_goals try with_reducible_and_instances rfl
    ring_nf
  have hmidNorm : Tendsto (fun n => ‖Dm n‖) atTop (𝓝 ‖D‖) := by
    apply tendsto_order.mpr
    refine ⟨hlow, fun b hb => ?_⟩
    filter_upwards [hmajor.eventually (gt_mem_nhds hb)] with n hn'
    exact (hupper n).trans_lt hn'
  have hsq (n : ℕ) : ‖Dn n - D‖^2 = 2*‖Dn n‖^2+2*‖D‖^2-4*‖Dm n‖^2 := by
    have hm : ‖Dm n‖ = ‖Dn n+D‖/2 := by
      simp only [Dm, ← smul_add, norm_smul,
        Real.norm_of_nonneg (by norm_num : (0 : ℝ) ≤ 1/2)]
      ring
    rw [hm]
    nlinarith [parallelogram_law_with_norm ℝ (Dn n) D]
  have hs : Tendsto (fun n => ‖Dn n-D‖^2) atTop (𝓝 0) := by
    simp_rw [hsq]
    convert ((hNorm.pow 2).const_mul 2 |>.add_const (2*‖D‖^2)).sub
      ((hmidNorm.pow 2).const_mul 4) using 1
    all_goals try with_reducible_and_instances rfl
    ring_nf
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  have H := Real.continuous_sqrt.continuousAt.tendsto.comp hs
  simpa only [Function.comp_def, Real.sqrt_sq_eq_abs, abs_norm, Real.sqrt_zero] using H

omit [BorelSpace X] in
lemma IsMinimalLocalWeakUpperGradient.norm_le {f D : Lp ℝ 2 m}
    (hD : IsMinimalLocalWeakUpperGradient m (f : X → ℝ) D)
    {E : Lp ℝ 2 m} (hE : IsLocalWeakUpperGradient m f E) : ‖D‖ ≤ ‖E‖ := by
  apply Lp.norm_le_norm_of_ae_le
  filter_upwards [hD.2 E hE, hD.1.2.1, hE.2.1] with x hx hd he
  simpa only [Real.norm_eq_abs, abs_of_nonneg hd, abs_of_nonneg he] using hx

lemma IsMinimalLocalWeakUpperGradient.tendsto_of_norm_tendsto
    {fn Dn : ℕ → Lp ℝ 2 m} {f D : Lp ℝ 2 m}
    (hD : IsMinimalLocalWeakUpperGradient m (f : X → ℝ) D)
    (hn : ∀ n, IsLocalWeakUpperGradient m (fn n) (Dn n))
    (hf : Tendsto fn atTop (𝓝 f))
    (hNorm : Tendsto (fun n => ‖Dn n‖) atTop (𝓝 ‖D‖)) :
    Tendsto Dn atTop (𝓝 D) :=
  upperGradient_tendsto_of_norm_tendsto hn hf hD.1 (fun _ hE => hD.norm_le hE) hNorm
end NormConvergence

open WeakHessianFunctional MeasureTheory Set Filter
open scoped Topology InnerProductSpace

end WeakHessian

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

end

end OAI
end

section
-- module Solutions.OAIQ52_WH.WeakHessian_LocalBounds_ChangeLpLp
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile0
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

noncomputable section
open scoped ENNReal NNReal Topology BoundedContinuousFunction CompactlySupported
open scoped ENNReal NNReal Topology BoundedContinuousFunction
open MeasureTheory
open scoped ENNReal InnerProductSpace ComplexConjugate
open Set MeasureTheory CompactlySupported CompactlySupportedContinuousMap
open scoped Topology ENNReal NNReal InnerProductSpace
open scoped BoundedContinuousFunction
open Set MeasureTheory Filter
open Set Filter MeasureTheory Topology TopologicalSpace
open scoped ENNReal NNReal
open Set MeasureTheory ProbabilityTheory
open scoped ENNReal MeasureTheory ProbabilityTheory
open Set Filter
open scoped ENNReal NNReal Topology InnerProductSpace
open Set Filter Bornology
open scoped Topology
open Set Filter Topology Bornology
open scoped InnerProductSpace

attribute [local instance] Classical.propDecidable
open Set
open scoped NNReal
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology
open MeasureTheory Set Filter
open scoped Topology ENNReal NNReal

namespace WeakHessian
open MeasureTheory Filter
open scoped Topology InnerProductSpace

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
variable {m ν : Measure X}

omit [MetricSpace X] [BorelSpace X] in
lemma changeLp_toLp {c : ℝ≥0∞} (hc : c ≠ ∞) (hν : ν ≤ c • m)
    {f : X → ℝ} (hf : MemLp f 2 m) :
    Lp.LpToLpOfMeasureLeSMul hc hν (hf.toLp f) =
      (hf.of_measure_le_smul hc hν).toLp f := by
  apply Lp.ext
  exact (Lp.coeFn_LpToLpOfMeasureLeSMul hc hν (hf.toLp f)).trans
    (((Measure.absolutelyContinuous_of_le_smul hν).ae_eq hf.coeFn_toLp).trans
      (hf.of_measure_le_smul hc hν).coeFn_toLp.symm)

omit [MetricSpace X] [BorelSpace X] in
lemma tendsto_toLp_changeMeasure {c : ℝ≥0∞} (hc : c ≠ ∞) (hν : ν ≤ c • m)
    {fs : ℕ → X → ℝ} {f : X → ℝ} (hfs : ∀ n, MemLp (fs n) 2 m) (hf : MemLp f 2 m)
    (h : Tendsto (fun n => (hfs n).toLp (fs n)) atTop (𝓝 (hf.toLp f))) :
    Tendsto (fun n => ((hfs n).of_measure_le_smul hc hν).toLp (fs n))
      atTop (𝓝 ((hf.of_measure_le_smul hc hν).toLp f)) := by
  have H := (Lp.LpToLpOfMeasureLeSMul (E := ℝ) (p := 2) hc hν).continuous.tendsto _ |>.comp h
  simpa only [Function.comp_def, changeLp_toLp] using H

omit [BorelSpace X] in
lemma FiniteOnBoundedSets.of_measure_le_smul (hm : FiniteOnBoundedSets m)
    {c : ℝ≥0∞} (hc : c ≠ ∞) (hν : ν ≤ c • m) : FiniteOnBoundedSets ν := by
  intro B hB
  exact lt_of_le_of_lt (hν B) (by
    rw [Measure.smul_apply, smul_eq_mul]
    exact ENNReal.mul_lt_top hc.lt_top (hm B hB))

end WeakHessian

end
end InlinedFile0

end OAI
end

section
-- module Solutions.OAIQ52_WH.WeakHessian_Sobolev_UpperGradientNormTendsto
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

noncomputable section
open scoped ENNReal NNReal Topology BoundedContinuousFunction CompactlySupported
open scoped ENNReal NNReal Topology BoundedContinuousFunction
open scoped NNReal
open MeasureTheory Set Filter
open scoped Topology NNReal ENNReal
open scoped ENNReal NNReal Topology InnerProductSpace
open Set Filter Bornology
open MeasureTheory
open scoped ENNReal InnerProductSpace ComplexConjugate
open scoped Topology
open Set Filter
open scoped Topology ENNReal NNReal
open Set
open Set MeasureTheory CompactlySupported CompactlySupportedContinuousMap
open scoped Topology ENNReal NNReal InnerProductSpace
open scoped BoundedContinuousFunction
open Set MeasureTheory Filter
open Set Filter MeasureTheory Topology TopologicalSpace
open scoped ENNReal NNReal
open Set MeasureTheory ProbabilityTheory
open scoped ENNReal MeasureTheory ProbabilityTheory
open Set Filter Topology Bornology
open scoped InnerProductSpace
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

attribute [local instance] Classical.propDecidable

open Set Filter Topology Bornology
open scoped InnerProductSpace


namespace WeakHessian
open MeasureTheory Filter
open scoped Topology InnerProductSpace

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
variable {m : Measure X}

lemma upperGradient_norm_tendsto_of_sq_upper {fn Dn : ℕ → Lp ℝ 2 m} {f D : Lp ℝ 2 m}
    (hn : ∀ n, IsLocalWeakUpperGradient m (fn n) (Dn n))
    (hf : Tendsto fn atTop (𝓝 f))
    (hmin : ∀ E : Lp ℝ 2 m, IsLocalWeakUpperGradient m f E → ‖D‖ ≤ ‖E‖)
    {ε : ℕ → ℝ} (hε : Tendsto ε atTop (𝓝 0))
    (hbound : ∀ n, ‖Dn n‖^2 ≤ ‖D‖^2+ε n) :
    Tendsto (fun n => ‖Dn n‖) atTop (𝓝 ‖D‖) := by
  apply tendsto_order.mpr
  constructor
  · intro a ha
    have hout : f ∈ {u : Lp ℝ 2 m | ∃ E : Lp ℝ 2 m,
        IsLocalWeakUpperGradient m u E ∧ ‖E‖ ≤ a}ᶜ := by
      rintro ⟨E,hE,he⟩
      exact (not_le_of_gt ha) ((hmin E hE).trans he)
    filter_upwards [hf.eventually
      ((isClosed_upperGradient_sublevel (m := m) a).isOpen_compl.mem_nhds hout)] with n hn'
    exact lt_of_not_ge (fun hle => hn' ⟨Dn n,hn n,hle⟩)
  · intro b hb
    have hbpos : 0 < b := lt_of_le_of_lt (norm_nonneg D) hb
    have hgap : 0 < b^2-‖D‖^2 := by nlinarith [norm_nonneg D]
    filter_upwards [hε.eventually (gt_mem_nhds hgap)] with n hn'
    nlinarith [hbound n, norm_nonneg (Dn n)]

lemma exists_lipschitz_strong_slopes (hfinite : FiniteOnBoundedSets m)
    {f D : Lp ℝ 2 m} (hD : IsMinimalLocalWeakUpperGradient m (f : X → ℝ) D)
    (henergy : cheegerEnergy m (f : X → ℝ) = ENNReal.ofReal (‖D‖^2/2)) :
    ∃ fs : ℕ → X → ℝ, (∀ n, GloballyLipschitz (fs n)) ∧
      ∃ hfs : ∀ n, MemLp (fs n) 2 m,
      ∃ hDs : ∀ n, MemLp (fun x => (localSlope (fs n) x).toReal) 2 m,
        Tendsto (fun n => (hfs n).toLp (fs n)) atTop (𝓝 f) ∧
        Tendsto (fun n => (hDs n).toLp (fun x => (localSlope (fs n) x).toReal))
          atTop (𝓝 D) := by
  have hex (n : ℕ) := cheegerEnergy_lt_approx (f := f)
    (a := ENNReal.ofReal (‖D‖^2/2+1/((n:ℝ)+1)))
    (by rw [henergy]; exact ENNReal.ofReal_lt_ofReal_iff_of_nonneg (by positivity) |>.mpr (lt_add_of_pos_right _ (by positivity)))
    (ε := 1/((n:ℝ)+1)) (by positivity)
  choose fs hLip hfs hdist hEn using hex
  have hfin (n : ℕ) : (∫⁻ x, (localSlope (fs n) x)^2 ∂m) < ∞ := by
    by_contra hh
    have ht : (∫⁻ x, (localSlope (fs n) x)^2 ∂m) = ∞ := top_le_iff.mp (not_lt.mp hh)
    have H := hEn n
    norm_num [ht] at H
  let hDs (n : ℕ) : MemLp (fun x => (localSlope (fs n) x).toReal) 2 m :=
    memLp_localSlope_of_lintegral_lt_top (hLip n).choose_spec (hfin n)
  let fn (n : ℕ) := (hfs n).toLp (fs n)
  let Dn (n : ℕ) := (hDs n).toLp (fun x => (localSlope (fs n) x).toReal)
  have hfn : Tendsto fn atTop (𝓝 f) := by
    apply tendsto_iff_dist_tendsto_zero.mpr
    exact squeeze_zero (fun _ => dist_nonneg) (fun n => (hdist n).le)
      tendsto_one_div_add_atTop_nhds_zero_nat
  have hDn (n : ℕ) : IsLocalWeakUpperGradient m (fn n) (Dn n) := by
    exact (localSlope_isLocalWeakUpperGradient hfinite (hLip n).choose_spec).congr_ae
      (hfs n).coeFn_toLp.symm (hDs n).coeFn_toLp.symm
  have hbound (n : ℕ) : ‖Dn n‖^2 ≤ ‖D‖^2 + 2*(1/((n:ℝ)+1)) := by
    have H := hEn n
    rw [half_lintegral_localSlope_eq (hLip n).choose_spec (hDs n)] at H
    have H' : ‖Dn n‖^2/2 < ‖D‖^2/2+1/((n:ℝ)+1) :=
      (ENNReal.ofReal_lt_ofReal_iff_of_nonneg (by positivity)).mp H
    linarith
  refine ⟨fs,hLip,hfs,hDs,hfn,?_⟩
  apply hD.tendsto_of_norm_tendsto hDn hfn
  exact upperGradient_norm_tendsto_of_sq_upper hDn hfn (fun _ hE => hD.norm_le hE)
    (by simpa using (tendsto_one_div_add_atTop_nhds_zero_nat.const_mul (2 : ℝ))) hbound

end WeakHessian

end

end OAI
end

section
-- module Solutions.OAIQ52_WH.WeakHessian_Sobolev_CheegerEnergyComparable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

noncomputable section
open scoped ENNReal NNReal Topology BoundedContinuousFunction CompactlySupported
open scoped ENNReal NNReal Topology BoundedContinuousFunction
open scoped NNReal
open MeasureTheory Set Filter
open scoped Topology NNReal ENNReal
open scoped ENNReal NNReal Topology InnerProductSpace
open Set Filter Bornology
open MeasureTheory
open scoped ENNReal InnerProductSpace ComplexConjugate
open scoped Topology
open Set Filter
open scoped Topology ENNReal NNReal
open Set
open Set MeasureTheory CompactlySupported CompactlySupportedContinuousMap
open scoped Topology ENNReal NNReal InnerProductSpace
open scoped BoundedContinuousFunction
open Set MeasureTheory Filter
open Set Filter MeasureTheory Topology TopologicalSpace
open scoped ENNReal NNReal
open Set MeasureTheory ProbabilityTheory
open scoped ENNReal MeasureTheory ProbabilityTheory
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

attribute [local instance] Classical.propDecidable
open Set Filter Topology Bornology
open scoped InnerProductSpace

namespace WeakHessian
open MeasureTheory Filter
open scoped Topology InnerProductSpace

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
variable {m ν : Measure X}

lemma cheegerEnergy_eq_of_comparable [CompleteSpace X] [TopologicalSpace.SeparableSpace X] (hfinite : FiniteOnBoundedSets m)
    {C E : ℝ≥0} (hm : m ≤ (C : ℝ≥0∞) • ν) (hν : ν ≤ (E : ℝ≥0∞) • m)
    {f D : Lp ℝ 2 m} (hD : IsMinimalLocalWeakUpperGradient m (f : X → ℝ) D)
    (henergy : cheegerEnergy m (f : X → ℝ) = ENNReal.ofReal (‖D‖^2/2)) :
    cheegerEnergy ν (f : X → ℝ) =
      ENNReal.ofReal (‖Lp.LpToLpOfMeasureLeSMul ENNReal.coe_ne_top hν D‖^2/2) := by
  let T : Lp ℝ 2 m →L[ℝ] Lp ℝ 2 ν := Lp.LpToLpOfMeasureLeSMul ENNReal.coe_ne_top hν
  obtain ⟨fs,hLip,hfs,hDs,hf,hG⟩ := exists_lipschitz_strong_slopes hfinite hD henergy
  have hfn := tendsto_toLp_changeMeasure ENNReal.coe_ne_top hν hfs (Lp.memLp f)
    (by simpa only [Lp.toLp_coeFn] using hf)
  have hDn := tendsto_toLp_changeMeasure ENNReal.coe_ne_top hν hDs (Lp.memLp D)
    (by simpa only [Lp.toLp_coeFn] using hG)
  have hDf : ((Lp.memLp D).of_measure_le_smul ENNReal.coe_ne_top hν).toLp (D : X → ℝ) = T D := rfl
  rw [hDf] at hDn
  have he : Tendsto (fun n => (2 : ℝ≥0∞)⁻¹ *
      ∫⁻ x, (localSlope (fs n) x)^2 ∂ν) atTop (𝓝 (ENNReal.ofReal (‖T D‖^2/2))) := by
    have H := ENNReal.continuous_ofReal.continuousAt.tendsto.comp ((hDn.norm.pow 2).div_const 2)
    convert H using 1
    all_goals try with_reducible_and_instances rfl
    funext n
    exact half_lintegral_localSlope_eq (hLip n).choose_spec
      ((hDs n).of_measure_le_smul ENNReal.coe_ne_top hν)
  have hle : cheegerEnergy ν (f : X → ℝ) ≤ ENNReal.ofReal (‖T D‖^2/2) := by
    have H := cheegerEnergy_le_liminf
      ((Lp.memLp f).of_measure_le_smul ENNReal.coe_ne_top hν)
      (fun n => ⟨hLip n,(hfs n).of_measure_le_smul ENNReal.coe_ne_top hν⟩)
      ((Lp.tendsto_Lp_iff_tendsto_eLpNorm'' fs
        (fun n => (hfs n).of_measure_le_smul ENNReal.coe_ne_top hν)
        (f : X → ℝ) ((Lp.memLp f).of_measure_le_smul ENNReal.coe_ne_top hν)).mp hfn)
    rwa [he.liminf_eq] at H
  have hDν : IsMinimalLocalWeakUpperGradient ν (f : X → ℝ) (T D) :=
    (hD.change_measure hm hν).congr_ae Filter.EventuallyEq.rfl
      (Lp.coeFn_LpToLpOfMeasureLeSMul ENNReal.coe_ne_top hν D).symm
  obtain ⟨D',hD',hlo⟩ := exists_minimalGradient_energy_le_cheeger
    (hfinite.of_measure_le_smul ENNReal.coe_ne_top hν)
    ((Lp.memLp f).of_measure_le_smul ENNReal.coe_ne_top hν)
    (lt_of_le_of_lt hle ENNReal.ofReal_lt_top)
  have heq : D' = T D := Lp.ext (hD'.ae_eq hDν)
  rw [heq] at hlo
  exact le_antisymm hle hlo

end WeakHessian

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

end

end OAI
end

section
-- module Solutions.OAIQ52_WH.WeakHessian_Sobolev_SobolevCheegerEnergyTop
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile0
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

noncomputable section
open scoped ENNReal NNReal Topology BoundedContinuousFunction CompactlySupported
open scoped ENNReal NNReal Topology BoundedContinuousFunction
open scoped NNReal
open MeasureTheory Set Filter
open scoped Topology NNReal ENNReal
open scoped ENNReal NNReal Topology InnerProductSpace
open Set Filter Bornology
open MeasureTheory
open scoped ENNReal InnerProductSpace ComplexConjugate
open Set Filter
open scoped Topology ENNReal NNReal
open Set
open Set MeasureTheory CompactlySupported CompactlySupportedContinuousMap
open scoped Topology ENNReal NNReal InnerProductSpace
open scoped BoundedContinuousFunction
open Set MeasureTheory Filter
open Set Filter MeasureTheory Topology TopologicalSpace
open scoped ENNReal NNReal
open Set MeasureTheory ProbabilityTheory
open scoped ENNReal MeasureTheory ProbabilityTheory
open Set Filter Topology Bornology
open scoped InnerProductSpace
open Filter
open scoped Topology

attribute [local instance] Classical.propDecidable
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

namespace WeakHessian
open MeasureTheory Filter
open scoped Topology InnerProductSpace

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
variable [CompleteSpace X] [TopologicalSpace.SeparableSpace X] {m ν : Measure X}

lemma cheegerEnergy_integral_of_comparable (hfinite : FiniteOnBoundedSets m)
    (hID : ∀ f : X → ℝ, Sobolev m f → cheegerEnergy m f =
      ENNReal.ofReal ((∫ x, (weakGradient m f x)^2 ∂m)/2))
    {C E : ℝ≥0} (hm : m ≤ (C : ℝ≥0∞) • ν) (hν : ν ≤ (E : ℝ≥0∞) • m)
    {f : X → ℝ} (hf : Sobolev m f) :
    cheegerEnergy ν f = ENNReal.ofReal ((∫ x, (weakGradient m f x)^2 ∂ν)/2) := by
  let f' := hf.1.toLp f
  let D' := hf.2.2.toLp (weakGradient m f)
  have hD : IsMinimalLocalWeakUpperGradient m (f' : X → ℝ) (D' : X → ℝ) :=
    (weakGradient_isMinimal hf.2.1.2).congr_ae hf.1.coeFn_toLp.symm hf.2.2.coeFn_toLp.symm
  have he : cheegerEnergy m (f' : X → ℝ) = ENNReal.ofReal (‖D'‖^2/2) := by
    rw [cheegerEnergy_congr_ae hf.1.coeFn_toLp,hID f hf,norm_toLp_sq_eq_integral]
  have H := cheegerEnergy_eq_of_comparable hfinite hm hν hD he
  have ha : (f' : X → ℝ) =ᵐ[ν] f := (Measure.absolutelyContinuous_of_le_smul hν).ae_eq hf.1.coeFn_toLp
  rw [cheegerEnergy_congr_ae ha] at H
  rw [H]
  congr 2
  let Dν := Lp.LpToLpOfMeasureLeSMul ENNReal.coe_ne_top hν D'
  have heq : Dν = (hf.2.2.of_measure_le_smul ENNReal.coe_ne_top hν).toLp (weakGradient m f) :=
    changeLp_toLp ENNReal.coe_ne_top hν hf.2.2
  change ‖Dν‖^2 = _
  rw [heq,norm_toLp_sq_eq_integral]

lemma quadraticCheegerEnergy_of_comparable [ProperSpace X]
    (hfinite : FiniteOnBoundedSets m) (h : QuadraticCheegerEnergy m)
    (hID : ∀ f : X → ℝ, Sobolev m f → cheegerEnergy m f =
      ENNReal.ofReal ((∫ x, (weakGradient m f x)^2 ∂m)/2))
    {C E : ℝ≥0} (hm : m ≤ (C : ℝ≥0∞) • ν) (hν : ν ≤ (E : ℝ≥0∞) • m) :
    QuadraticCheegerEnergy ν := by
  intro f g hf hg
  have hfiniteν := hfinite.of_measure_le_smul ENNReal.coe_ne_top hν
  have hfm : Sobolev m f := (sobolev_iff_of_comparable hν hm f).mp
    (sobolev_of_cheegerEnergy_lt_top hfiniteν hf)
  have hgm : Sobolev m g := (sobolev_iff_of_comparable hν hm g).mp
    (sobolev_of_cheegerEnergy_lt_top hfiniteν hg)
  have hp := hfm.add hfinite hgm
  have hn := hfm.sub hfinite hgm
  have hpar := weakGradient_pointwise_parallelogram hfinite
    (fun _ _ hf hg => integral_parallelogram_of_cheeger hfinite h hID hf hg) hfm hgm
  have hparν := (Measure.absolutelyContinuous_of_le_smul hν).ae_le hpar
  have hpf := (hp.2.2.of_measure_le_smul ENNReal.coe_ne_top hν).integrable_sq
  have hnf := (hn.2.2.of_measure_le_smul ENNReal.coe_ne_top hν).integrable_sq
  have hff := (hfm.2.2.of_measure_le_smul ENNReal.coe_ne_top hν).integrable_sq
  have hgf := (hgm.2.2.of_measure_le_smul ENNReal.coe_ne_top hν).integrable_sq
  have hi : (∫ x, (weakGradient m (fun y => f y+g y) x)^2 ∂ν) +
      (∫ x, (weakGradient m (fun y => f y-g y) x)^2 ∂ν) =
    2*(∫ x, (weakGradient m f x)^2 ∂ν) + 2*(∫ x, (weakGradient m g x)^2 ∂ν) := by
    rw [← integral_add hpf hnf, ← integral_const_mul 2, ← integral_const_mul 2,
      ← integral_add (hff.const_mul 2) (hgf.const_mul 2)]
    exact integral_congr_ae hparν
  rw [cheegerEnergy_integral_of_comparable hfinite hID hm hν hp,
    cheegerEnergy_integral_of_comparable hfinite hID hm hν hn,
    cheegerEnergy_integral_of_comparable hfinite hID hm hν hfm,
    cheegerEnergy_integral_of_comparable hfinite hID hm hν hgm]
  have hp0 : 0 ≤ (∫ x, (weakGradient m (fun y => f y+g y) x)^2 ∂ν)/2 := by positivity
  have hn0 : 0 ≤ (∫ x, (weakGradient m (fun y => f y-g y) x)^2 ∂ν)/2 := by positivity
  have hf0 : 0 ≤ (∫ x, (weakGradient m f x)^2 ∂ν)/2 := by positivity
  have hg0 : 0 ≤ (∫ x, (weakGradient m g x)^2 ∂ν)/2 := by positivity
  rw [← ENNReal.ofReal_add hp0 hn0, ← ENNReal.ofReal_ofNat 2,
    ← ENNReal.ofReal_mul (by norm_num), ← ENNReal.ofReal_mul (by norm_num),
    ← ENNReal.ofReal_add (by positivity) (by positivity)]
  congr 1
  linarith
end WeakHessian

end
end InlinedFile0

end OAI
end

section
-- module Solutions.OAIQ52_WH.WeakHessian_Geodesics_MidpointSigmaLower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile0
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

noncomputable section
open scoped ENNReal NNReal Topology BoundedContinuousFunction CompactlySupported
open scoped ENNReal NNReal Topology BoundedContinuousFunction
open scoped NNReal
open MeasureTheory Set Filter
open scoped Topology NNReal ENNReal
open scoped ENNReal NNReal Topology InnerProductSpace
open Set Filter Bornology
open MeasureTheory
open scoped ENNReal InnerProductSpace ComplexConjugate
open Set Filter
open scoped Topology ENNReal NNReal
open Set
open Set MeasureTheory CompactlySupported CompactlySupportedContinuousMap
open scoped Topology ENNReal NNReal InnerProductSpace
open scoped BoundedContinuousFunction
open Set MeasureTheory Filter
open Set Filter MeasureTheory Topology TopologicalSpace
open scoped ENNReal NNReal
open Set MeasureTheory ProbabilityTheory
open scoped ENNReal MeasureTheory ProbabilityTheory
open Set Filter Topology Bornology
open scoped InnerProductSpace
open Filter
open scoped Topology
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

attribute [local instance] Classical.propDecidable
namespace WeakHessian
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]

lemma cd_iterated_ball_volume {m : Measure X} {K N : ℝ} (hN : 1 < N)
    (hCD : CurvatureDimension m K N) (hfull : FullSupport m)
    (hfin : FiniteOnBoundedSets m) (o : X) {R : ℝ} (hR : 0 < R) (n : ℕ) :
    (midpointTauLower K N (2*R))^n * (m (Metric.ball o R))^(1/N) ≤
      (m (Metric.ball o ((3/4 : ℝ)^n*R)))^(1/N) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hr : 0 < (3/4 : ℝ)^n * R := mul_pos (pow_pos (by norm_num) _) hR
    have hrle : (3/4 : ℝ)^n * R ≤ R := by
      nlinarith [pow_le_one₀ (n := n) (by norm_num : 0 ≤ (3/4 : ℝ)) (by norm_num)]
    have hs := cd_midpoint_ball_volume hN hCD hfull hfin o hr
      (show 2*((3/4 : ℝ)^n*R) ≤ 2*R by linarith)
    calc
      (midpointTauLower K N (2*R))^(n+1) * (m (Metric.ball o R))^(1/N) =
          midpointTauLower K N (2*R) *
            ((midpointTauLower K N (2*R))^n * (m (Metric.ball o R))^(1/N)) := by
        rw [pow_succ]; ac_rfl
      _ ≤ midpointTauLower K N (2*R) *
          (m (Metric.ball o ((3/4 : ℝ)^n*R)))^(1/N) := mul_le_mul_right ih _
      _ ≤ (m (Metric.ball o ((3/4 : ℝ)^(n+1)*R)))^(1/N) := by
        have he : 3*((3/4 : ℝ)^n*R)/4 = (3/4 : ℝ)^(n+1)*R := by
          rw [pow_succ]; ring
        simpa only [he] using hs

lemma cd_uniform_ball_measure_lower {m : Measure X} {K N : ℝ} (hN : 1 < N)
    (hCD : CurvatureDimension m K N) (hfull : FullSupport m)
    (hfin : FiniteOnBoundedSets m) (o : X) {R r : ℝ} (hR : 0 ≤ R) (hr : 0 < r) :
    ∃ δ : ℝ≥0∞, 0 < δ ∧ δ ≠ ∞ ∧
      ∀ x ∈ Metric.closedBall o R, δ ≤ m (Metric.ball x r) := by
  let S := 2*R+2
  have hS : 0 < S := by dsimp [S]; linarith
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one (div_pos hr hS) (by norm_num : (3/4 : ℝ) < 1)
  have hn' : (3/4 : ℝ)^n*S < r := (lt_div_iff₀ hS).mp hn
  let p : ℝ≥0∞ := (midpointTauLower K N (2*S))^n * (m (Metric.ball o 1))^(1/N)
  have hbase : 0 < m (Metric.ball o 1) :=
    hfull _ Metric.isOpen_ball ⟨o, Metric.mem_ball_self zero_lt_one⟩
  have hbasefin : m (Metric.ball o 1) ≠ ∞ := (hfin _ Metric.isBounded_ball).ne
  have hp : 0 < p := ENNReal.mul_pos_iff.mpr
    ⟨ENNReal.pow_pos (midpointTauLower_pos _ _ _) _, ENNReal.rpow_pos hbase hbasefin⟩
  have hpfin : p ≠ ∞ := ENNReal.mul_ne_top
    (ENNReal.pow_ne_top (midpointTauLower_ne_top hN))
    (ENNReal.rpow_ne_top_of_nonneg (by positivity) hbasefin)
  refine ⟨p^N, ENNReal.rpow_pos hp hpfin,
    ENNReal.rpow_ne_top_of_nonneg (by linarith) hpfin, ?_⟩
  intro x hx
  have hsub : Metric.ball o 1 ⊆ Metric.ball x S := by
    apply Metric.ball_subset_ball'
    have hx' : dist x o ≤ R := hx
    rw [dist_comm o]
    dsimp [S]
    linarith
  have hlow : p ≤ (m (Metric.ball x r))^(1/N) := by
    calc
      p ≤ (midpointTauLower K N (2*S))^n * (m (Metric.ball x S))^(1/N) :=
        mul_le_mul_right (ENNReal.rpow_le_rpow (measure_mono hsub) (by positivity)) _
      _ ≤ (m (Metric.ball x ((3/4 : ℝ)^n*S)))^(1/N) :=
        cd_iterated_ball_volume hN hCD hfull hfin x hS n
      _ ≤ (m (Metric.ball x r))^(1/N) :=
        ENNReal.rpow_le_rpow (measure_mono (Metric.ball_subset_ball hn'.le)) (by positivity)
  have hh := ENNReal.rpow_le_rpow hlow (show 0 ≤ N by linarith)
  rwa [← ENNReal.rpow_mul, div_mul_cancel₀ 1 (show N ≠ 0 by linarith), ENNReal.rpow_one] at hh

lemma properSpace_of_cd [CompleteSpace X] [SecondCountableTopology X]
    {m : Measure X} {K N : ℝ} (hN : 1 < N) (hCD : CurvatureDimension m K N)
    (hfull : FullSupport m) (hfin : FiniteOnBoundedSets m) : ProperSpace X := by
  constructor
  intro o R
  apply isCompact_iff_totallyBounded_isComplete.mpr
  refine ⟨?_, Metric.isClosed_closedBall.isComplete⟩
  apply Metric.totallyBounded_iff.mpr
  intro r hr
  obtain ⟨δ, hδ, _, hvol⟩ := cd_uniform_ball_measure_lower hN hCD hfull hfin o
    (le_max_right R 0) (half_pos hr)
  let U := Metric.ball o (max R 0+r+1)
  let ν := m.restrict U
  let : IsFiniteMeasure ν := isFiniteMeasure_restrict.mpr (hfin U Metric.isBounded_ball).ne
  obtain ⟨S, hS, hsmall⟩ := exists_isCompact_closure_measure_compl_lt ν δ hδ
  have hsmall' : ν (closure S)ᶜ < δ :=
    (measure_mono (compl_subset_compl.mpr subset_closure)).trans_lt hsmall
  obtain ⟨T, hTfin, hcover⟩ := Metric.totallyBounded_iff.mp hS.totallyBounded (r/2) (half_pos hr)
  refine ⟨T, hTfin, ?_⟩
  intro x hx
  have hx' : dist x o ≤ max R 0 := (show dist x o ≤ R from hx).trans (le_max_left _ _)
  have hU : Metric.ball x (r/2) ⊆ U := by
    apply Metric.ball_subset_ball'
    linarith
  have hν : δ ≤ ν (Metric.ball x (r/2)) := by
    change δ ≤ (m.restrict U) (Metric.ball x (r/2))
    rw [Measure.restrict_apply Metric.isOpen_ball.measurableSet, inter_eq_left.mpr hU]
    exact hvol x hx'
  have hinter : (Metric.ball x (r/2) ∩ closure S).Nonempty := by
    by_contra hempty
    have hsub : Metric.ball x (r/2) ⊆ (closure S)ᶜ := by
      intro y hy hys
      exact hempty ⟨y, hy, hys⟩
    exact (not_le_of_gt hsmall') (hν.trans (measure_mono hsub))
  obtain ⟨y, hyball, hyS⟩ := hinter
  obtain ⟨z, hzT, hyz⟩ := mem_iUnion₂.mp (hcover hyS)
  apply mem_iUnion₂.mpr
  refine ⟨z, hzT, ?_⟩
  have hxy : dist x y < r/2 := by simpa only [Metric.mem_ball, dist_comm] using hyball
  have hyz' : dist y z < r/2 := hyz
  exact (dist_triangle x y z).trans_lt (by linarith)

end WeakHessian

end
end InlinedFile0

end OAI
end

section
-- module Solutions.OAIQ52_WH.WeakHessian_Geodesics_SquareControl
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

noncomputable section
open scoped ENNReal NNReal Topology BoundedContinuousFunction CompactlySupported
open scoped ENNReal NNReal Topology BoundedContinuousFunction
open scoped NNReal
open MeasureTheory Set Filter
open scoped Topology NNReal ENNReal
open scoped ENNReal NNReal Topology InnerProductSpace
open Set Filter Bornology
open MeasureTheory
open scoped ENNReal InnerProductSpace ComplexConjugate
open Set Filter
open scoped Topology ENNReal NNReal
open Set
open Set MeasureTheory CompactlySupported CompactlySupportedContinuousMap
open scoped Topology ENNReal NNReal InnerProductSpace
open scoped BoundedContinuousFunction
open Set MeasureTheory Filter
open Set Filter MeasureTheory Topology TopologicalSpace
open scoped ENNReal NNReal
open Set MeasureTheory ProbabilityTheory
open scoped ENNReal MeasureTheory ProbabilityTheory
open Set Filter Topology Bornology
open scoped InnerProductSpace
open Filter
open scoped Topology
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

attribute [local instance] Classical.propDecidable
namespace WeakHessian
open MeasureTheory Filter Set
open scoped Topology ENNReal NNReal

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]

omit [MeasurableSpace X] [BorelSpace X] in
lemma IsGeodesic.squareControl {γ : Curve X} (h : IsGeodesic γ) :
    IsSquareControl γ (fun _ => dist (γ timeZero) (γ timeOne)) := by
  refine ⟨measurable_const,memLp_const _,ae_of_all _ (fun _ => dist_nonneg),?_⟩
  intro s t hst
  rw [h s t,intervalIntegral.integral_const,smul_eq_mul,
    abs_sub_comm (s:ℝ),abs_of_nonneg (sub_nonneg.mpr hst)]

end WeakHessian

end

end OAI
end

section
-- module Solutions.OAIQ52_WH.WeakHessian_Entropy_FiniteEntropy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

noncomputable section
open scoped ENNReal NNReal Topology BoundedContinuousFunction CompactlySupported
open scoped ENNReal NNReal Topology BoundedContinuousFunction
open scoped NNReal
open MeasureTheory Set Filter
open scoped Topology NNReal ENNReal
open scoped ENNReal NNReal Topology InnerProductSpace
open Set Filter Bornology
open MeasureTheory
open scoped ENNReal InnerProductSpace ComplexConjugate
open Set Filter
open scoped Topology ENNReal NNReal
open Set
open Set MeasureTheory CompactlySupported CompactlySupportedContinuousMap
open scoped Topology ENNReal NNReal InnerProductSpace
open scoped BoundedContinuousFunction
open Set MeasureTheory Filter
open Set Filter MeasureTheory Topology TopologicalSpace
open scoped ENNReal NNReal
open Set MeasureTheory ProbabilityTheory
open scoped ENNReal MeasureTheory ProbabilityTheory
open Set Filter Topology Bornology
open scoped InnerProductSpace
open Filter
open scoped Topology
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

attribute [local instance] Classical.propDecidable

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

namespace WeakHessian

variable {X : Type*} [MeasurableSpace X]

lemma llr_exponentialMeasure {m μ : Measure X} [SigmaFinite m] [IsFiniteMeasure μ]
    {V : X → ℝ} (hμ : μ ≪ m) (hV : Measurable V) :
    llr μ (exponentialMeasure m V) =ᵐ[μ] fun x => llr μ m x - V x := by
  have hmeas : Measurable (fun x => ENNReal.ofReal (Real.exp (V x))) := by fun_prop
  have hpos : ∀ᵐ x ∂m, ENNReal.ofReal (Real.exp (V x)) ≠ 0 :=
    ae_of_all m fun x => (ENNReal.ofReal_pos.mpr (Real.exp_pos _)).ne'
  have htop : ∀ᵐ x ∂m, ENNReal.ofReal (Real.exp (V x)) ≠ ∞ :=
    ae_of_all m fun _ => ENNReal.ofReal_ne_top
  have hrn := Measure.rnDeriv_withDensity_right μ m hmeas.aemeasurable hpos htop
  filter_upwards [hμ.ae_eq hrn, Measure.rnDeriv_pos hμ,
    hμ.ae_le (Measure.rnDeriv_lt_top μ m)] with x hx hp ht
  change Real.log (μ.rnDeriv (exponentialMeasure m V) x).toReal =
    Real.log (μ.rnDeriv m x).toReal - V x
  dsimp only [exponentialMeasure]
  rw [hx, ENNReal.toReal_mul, ENNReal.toReal_inv,
    ENNReal.toReal_ofReal (Real.exp_pos _).le,
    Real.log_mul (inv_ne_zero (Real.exp_ne_zero _))
      (ENNReal.toReal_ne_zero.mpr ⟨hp.ne', ht.ne⟩), Real.log_inv, Real.log_exp]
  ring

theorem entropyReal_exponentialMeasure {m μ : Measure X}
    [SigmaFinite m] [IsFiniteMeasure μ] {V : X → ℝ}
    (hμ : FiniteEntropy m μ) (hV : Measurable V) (hVi : Integrable V μ) :
    entropyReal (exponentialMeasure m V) μ = entropyReal m μ - ∫ x, V x ∂μ := by
  rw [entropyReal, integral_congr_ae (llr_exponentialMeasure hμ.1 hV),
    integral_sub hμ.2 hVi, entropyReal]

end WeakHessian

open Set Filter MeasureTheory InformationTheory
open scoped Topology

end

end OAI
end

section
-- module Solutions.OAIQ52_WH.WeakHessian_Entropy_MulLogFenchel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile0
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

noncomputable section
open scoped ENNReal NNReal Topology BoundedContinuousFunction CompactlySupported
open scoped ENNReal NNReal Topology BoundedContinuousFunction
open scoped NNReal
open MeasureTheory Set Filter
open scoped Topology NNReal ENNReal
open scoped ENNReal NNReal Topology InnerProductSpace
open Set Filter Bornology
open MeasureTheory
open scoped ENNReal InnerProductSpace ComplexConjugate
open scoped Topology ENNReal NNReal
open Set
open Set MeasureTheory CompactlySupported CompactlySupportedContinuousMap
open scoped Topology ENNReal NNReal InnerProductSpace
open Set MeasureTheory Filter
open Set Filter MeasureTheory Topology TopologicalSpace
open scoped ENNReal NNReal
open Filter
open Set Filter MeasureTheory InformationTheory
open Set Filter
open scoped Topology
open Set MeasureTheory ProbabilityTheory
open scoped ENNReal MeasureTheory ProbabilityTheory
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

attribute [local instance] Classical.propDecidable
open Set Filter Topology Bornology
open scoped InnerProductSpace
open scoped BoundedContinuousFunction
open Set Filter Topology

namespace WeakHessian
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology BoundedContinuousFunction

lemma mul_log_fenchel {r a : ℝ} (hr : 0 ≤ r) : r*a-Real.exp a+r ≤ r*Real.log r := by
  rcases hr.eq_or_lt with hr|hr
  · simp only [← hr,zero_mul,add_zero,sub_nonpos]
    exact (Real.exp_pos _).le
  · have H := Real.log_le_sub_one_of_pos (div_pos (Real.exp_pos a) hr)
    rw [Real.log_div (Real.exp_pos _).ne' hr.ne',Real.log_exp] at H
    have := (mul_le_mul_of_nonneg_left H hr.le)
    simp only [mul_sub,mul_div_cancel₀ _ hr.ne',mul_one] at this
    nlinarith

lemma mul_log_floor_gap {r δ : ℝ} (hr : 0 ≤ r) (hδ : 0 < δ) :
    r*Real.log r - (r*Real.log (max δ r)-max δ r+r) ≤ δ := by
  by_cases h : δ ≤ r
  · rw [max_eq_right h]
    linarith
  · have hrd : r ≤ δ := (le_of_not_ge h)
    rw [max_eq_left hrd]
    rcases hr.eq_or_lt with hr|hr
    · simp [← hr]
    · have H := mul_le_mul_of_nonneg_left (Real.log_le_log hr hrd) hr.le
      nlinarith

lemma exp_sub_bound {a b M : ℝ} (ha : a ≤ M) (hb : b ≤ M) :
    ‖Real.exp a-Real.exp b‖ ≤ Real.exp M*‖a-b‖ := by
  apply (convex_Iic M).norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun x _ => (Real.hasDerivAt_exp x).hasDerivWithinAt) ?_ hb ha
  intro x hx
  simpa only [Real.norm_eq_abs,abs_of_pos (Real.exp_pos x)] using Real.exp_le_exp.mpr hx

lemma min_sub_clamp {x a b : ℝ} (ha : a ≤ b) : ‖a-min x b‖ ≤ ‖a-x‖ := by
  simp only [Real.norm_eq_abs]
  by_cases hx : x ≤ b
  · simp [min_eq_left hx]
  · rw [min_eq_right (le_of_not_ge hx),abs_of_nonpos (sub_nonpos.mpr ha),
      abs_of_nonpos (sub_nonpos.mpr (ha.trans (le_of_not_ge hx)))]
    linarith

universe u
variable {X : Type u} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
variable {m μ : Measure X} [IsFiniteMeasure m] [IsFiniteMeasure μ]

lemma entropyReal_fenchel (hμ : FiniteEntropy m μ) (f : X →ᵇ ℝ) :
    (∫ x, f x ∂μ) - (∫ x, Real.exp (f x) ∂m) + μ.real univ ≤ entropyReal m μ := by
  have hfμ : Integrable (fun x => f x) μ := f.integrable μ
  have hm : Integrable (fun x => (μ.rnDeriv m x).toReal*f x) m :=
    (integrable_toReal_rnDeriv_mul_iff hμ.1).mpr hfμ
  have hr : Integrable (fun x => (μ.rnDeriv m x).toReal) m := by
    simpa only [mul_one] using (integrable_toReal_rnDeriv_mul_iff hμ.1).mpr (integrable_const (1:ℝ))
  have he : Integrable (fun x => Real.exp (f x)) m := by
    apply (integrable_const (Real.exp ‖f‖)).mono'
      (Real.continuous_exp.comp f.continuous).aestronglyMeasurable
    exact ae_of_all _ fun x => by
      simp only [Function.comp_apply,Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)]
      exact Real.exp_le_exp.mpr (le_trans (le_abs_self _) (f.norm_coe_le_norm x))
  have hlog : Integrable (fun x => (μ.rnDeriv m x).toReal * Real.log (μ.rnDeriv m x).toReal) m :=
    (integrable_rnDeriv_mul_log_iff hμ.1).mpr hμ.2
  have H := integral_mono (hm.sub he |>.add hr) hlog (fun x => mul_log_fenchel ENNReal.toReal_nonneg)
  simp only [Pi.add_apply,Pi.sub_apply] at H
  rw [integral_add (f := fun x => (μ.rnDeriv m x).toReal*f x-Real.exp (f x)) (hm.sub he) hr,integral_sub hm he,integral_toReal_rnDeriv_mul hμ.1,
    Measure.integral_toReal_rnDeriv hμ.1,← entropyReal_eq_integral_density hμ.1] at H
  exact H

end WeakHessian

end
end InlinedFile0

end OAI
end

section
-- module Solutions.OAIQ52_WH.WeakHessian_Measure_IntegrableExpBounded
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile0
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

noncomputable section
open scoped ENNReal NNReal Topology BoundedContinuousFunction CompactlySupported
open scoped ENNReal NNReal Topology BoundedContinuousFunction
open scoped NNReal
open MeasureTheory Set Filter
open scoped Topology NNReal ENNReal
open scoped ENNReal NNReal Topology InnerProductSpace
open Set Filter Bornology
open MeasureTheory
open scoped ENNReal InnerProductSpace ComplexConjugate
open scoped Topology ENNReal NNReal
open Set
open Set MeasureTheory CompactlySupported CompactlySupportedContinuousMap
open scoped Topology ENNReal NNReal InnerProductSpace
open Set MeasureTheory Filter
open Set Filter MeasureTheory Topology TopologicalSpace
open scoped ENNReal NNReal
open Filter
open Set Filter MeasureTheory InformationTheory
open Set Filter
open scoped Topology
open Set MeasureTheory ProbabilityTheory
open scoped ENNReal MeasureTheory ProbabilityTheory
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

attribute [local instance] Classical.propDecidable
open Set Filter Topology Bornology
open scoped InnerProductSpace
open scoped BoundedContinuousFunction
open Set Filter Topology

namespace WeakHessian
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology BoundedContinuousFunction

universe u
variable {X : Type u} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
variable [SecondCountableTopology X]
variable {m μ : Measure X} [IsFiniteMeasure m] [IsFiniteMeasure μ]

omit [MetricSpace X] [BorelSpace X] [SecondCountableTopology X] in
lemma integrable_exp_of_bounded {f : X → ℝ} (hf : Measurable f) {A : ℝ}
    (hA : ∀ x, f x ≤ A) (ν : Measure X) [IsFiniteMeasure ν] :
    Integrable (fun x => Real.exp (f x)) ν := by
  apply Integrable.of_bound (Real.measurable_exp.comp hf).aestronglyMeasurable (Real.exp A)
  exact ae_of_all _ fun x => by
    simp only [Function.comp_apply,Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)]
    exact Real.exp_le_exp.mpr (hA x)

lemma exists_continuous_fenchel_approx {f : X → ℝ} (hf : Measurable f) {A M : ℝ}
    (hA : ∀ x, ‖f x‖ ≤ A) (hM : 0 < M) (hfM : ∀ x, f x ≤ Real.log M)
    {ε : ℝ} (hε : 0 < ε) : ∃ g : X →ᵇ ℝ,
      (∫ x, f x ∂μ) - (∫ x, Real.exp (f x) ∂m) ≤
        (∫ x, g x ∂μ) - (∫ x, Real.exp (g x) ∂m) + ε := by
  let ν := μ+m
  have hfν : Integrable f ν := Integrable.of_bound hf.aestronglyMeasurable A (ae_of_all _ hA)
  let η := ε/(1+M)
  have hη : 0 < η := div_pos hε (by linarith)
  obtain ⟨h,hh,_⟩ := hfν.exists_boundedContinuous_integral_sub_le hη
  let g : X →ᵇ ℝ := h ⊓ BoundedContinuousFunction.const X (Real.log M)
  have hg (x : X) : g x = min (h x) (Real.log M) := rfl
  have hfg : Integrable (fun x => ‖f x-g x‖) ν := (hfν.sub (g.integrable ν)).norm
  have hL : (∫ x, ‖f x-g x‖ ∂ν) ≤ η := by
    apply le_trans (integral_mono hfg (hfν.sub (h.integrable ν)).norm ?_) hh
    intro x
    change ‖f x-g x‖ ≤ ‖f x-h x‖
    rw [hg]
    exact min_sub_clamp (hfM x)
  have hμν : μ ≤ ν := Measure.le_add_right le_rfl
  have hmν : m ≤ ν := Measure.le_add_left le_rfl
  have hfμ := hfν.mono_measure hμν
  have hμL : (∫ x, ‖f x-g x‖ ∂μ) ≤ η :=
    (integral_mono_measure hμν (ae_of_all _ fun _ => norm_nonneg _) hfg).trans hL
  have hmL : (∫ x, ‖f x-g x‖ ∂m) ≤ η :=
    (integral_mono_measure hmν (ae_of_all _ fun _ => norm_nonneg _) hfg).trans hL
  have hfirst : (∫ x, f x ∂μ) - (∫ x, g x ∂μ) ≤ η := by
    rw [← integral_sub hfμ (g.integrable μ)]
    exact (le_trans (Real.le_norm_self _) (norm_integral_le_integral_norm _)).trans hμL
  have hgM (x : X) : g x ≤ Real.log M := by rw [hg]; exact min_le_right _ _
  have heF := integrable_exp_of_bounded hf hfM m
  have heG := integrable_exp_of_bounded g.continuous.measurable hgM m
  have heDiff : (∫ x, Real.exp (g x) ∂m) - (∫ x, Real.exp (f x) ∂m) ≤ M*η := by
    calc
      _ = ∫ x, Real.exp (g x)-Real.exp (f x) ∂m := (integral_sub heG heF).symm
      _ ≤ ∫ x, M*‖f x-g x‖ ∂m := by
        apply integral_mono (heG.sub heF) ((hfg.mono_measure hmν).const_mul M)
        intro x
        have H := exp_sub_bound (hgM x) (hfM x)
        rw [Real.exp_log hM,norm_sub_rev (g x)] at H
        exact (le_trans (Real.le_norm_self _) H)
      _ = M*(∫ x, ‖f x-g x‖ ∂m) := integral_const_mul _ _
      _ ≤ M*η := mul_le_mul_of_nonneg_left hmL hM.le
  refine ⟨g,?_⟩
  have H : (1+M)*η = ε := mul_div_cancel₀ ε (by linarith : (1+M) ≠ 0)
  nlinarith

end WeakHessian

end
end InlinedFile0

end OAI
end

section
-- module Solutions.OAIQ52_WH.WeakHessian_Entropy_EntropyRealContinuousSupport
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile0
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

noncomputable section
open scoped ENNReal NNReal Topology BoundedContinuousFunction CompactlySupported
open scoped ENNReal NNReal Topology BoundedContinuousFunction
open scoped NNReal
open MeasureTheory Set Filter
open scoped Topology NNReal ENNReal
open scoped ENNReal NNReal Topology InnerProductSpace
open Set Filter Bornology
open MeasureTheory
open scoped ENNReal InnerProductSpace ComplexConjugate
open scoped Topology ENNReal NNReal
open Set
open Set MeasureTheory CompactlySupported CompactlySupportedContinuousMap
open scoped Topology ENNReal NNReal InnerProductSpace
open Set MeasureTheory Filter
open Set Filter MeasureTheory Topology TopologicalSpace
open scoped ENNReal NNReal
open Filter
open Set Filter MeasureTheory InformationTheory
open Set Filter
open scoped Topology
open Set MeasureTheory ProbabilityTheory
open scoped ENNReal MeasureTheory ProbabilityTheory
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

attribute [local instance] Classical.propDecidable
open Set Filter Topology Bornology
open scoped InnerProductSpace
open scoped BoundedContinuousFunction
open Set Filter Topology

namespace WeakHessian
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology BoundedContinuousFunction

universe u
variable {X : Type u} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
variable [SecondCountableTopology X]
variable {m μ : Measure X} [IsFiniteMeasure m] [IsFiniteMeasure μ]

lemma entropyReal_continuous_support {B : ℝ≥0∞} (hB : B ≠ ∞)
    (hd : μ ≤ B • m) {ε : ℝ} (hε : 0 < ε) : ∃ g : X →ᵇ ℝ,
      entropyReal m μ ≤ (∫ x, g x ∂μ) - (∫ x, Real.exp (g x) ∂m) + μ.real univ + ε := by
  have hμ := finiteEntropy_of_bounded_density hB hd
  let C := max 1 B.toReal
  have hC : 0 < C := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  let δ := ε/(4*(1+m.real univ))
  have hmnon : 0 ≤ m.real univ := ENNReal.toReal_nonneg
  have hδ : 0 < δ := div_pos hε (by positivity)
  let M := C+δ
  have hM : 0 < M := add_pos hC hδ
  let r := fun x => min (μ.rnDeriv m x).toReal C
  have hrnon (x : X) : 0 ≤ r x := le_min ENNReal.toReal_nonneg hC.le
  have hrC (x : X) : r x ≤ C := min_le_right _ _
  have hrEq : r =ᵐ[m] fun x => (μ.rnDeriv m x).toReal := by
    filter_upwards [rnDeriv_le_of_domination hd hμ.1] with x hx
    exact min_eq_left ((ENNReal.toReal_mono hB hx).trans (le_max_right _ _))
  let f := fun x => Real.log (max δ (r x))
  have hf : Measurable f := Real.measurable_log.comp
    (measurable_const.max ((Measure.measurable_rnDeriv μ m).ennreal_toReal.min measurable_const))
  have htpos (x : X) : 0 < max δ (r x) := lt_of_lt_of_le hδ (le_max_left _ _)
  have hflo (x : X) : Real.log δ ≤ f x :=
    Real.log_le_log hδ (le_max_left _ _)
  have hfM (x : X) : f x ≤ Real.log M :=
    Real.log_le_log (htpos x) (max_le (by dsimp [M]; linarith) (by dsimp [M]; linarith [hrC x]))
  let A := |Real.log δ|+|Real.log M|
  have hfA (x : X) : ‖f x‖ ≤ A := by
    rw [Real.norm_eq_abs]
    apply abs_le.mpr
    constructor
    · dsimp [A]
      have H := neg_abs_le (Real.log δ)
      linarith [hflo x,abs_nonneg (Real.log M)]
    · dsimp [A]
      have H := le_abs_self (Real.log M)
      linarith [hfM x,abs_nonneg (Real.log δ)]
  have hfμ : Integrable f μ := Integrable.of_bound hf.aestronglyMeasurable A (ae_of_all _ hfA)
  have hfm : Integrable f m := Integrable.of_bound hf.aestronglyMeasurable A (ae_of_all _ hfA)
  have he := integrable_exp_of_bounded hf hfM m
  have hrf : Integrable (fun x => (μ.rnDeriv m x).toReal*f x) m :=
    (integrable_toReal_rnDeriv_mul_iff hμ.1).mpr hfμ
  have hr : Integrable (fun x => (μ.rnDeriv m x).toReal) m := by
    simpa only [mul_one] using (integrable_toReal_rnDeriv_mul_iff hμ.1).mpr (integrable_const (1:ℝ))
  have hlog : Integrable (fun x => (μ.rnDeriv m x).toReal*Real.log (μ.rnDeriv m x).toReal) m :=
    (integrable_rnDeriv_mul_log_iff hμ.1).mpr hμ.2
  have hpoint : ∀ᵐ x ∂m, (μ.rnDeriv m x).toReal*Real.log (μ.rnDeriv m x).toReal ≤
      (μ.rnDeriv m x).toReal*f x-Real.exp (f x)+(μ.rnDeriv m x).toReal+δ := by
    filter_upwards [hrEq] with x hx
    have H := mul_log_floor_gap (r := (μ.rnDeriv m x).toReal) ENNReal.toReal_nonneg hδ
    have hfexp : Real.exp (f x) = max δ (μ.rnDeriv m x).toReal := by
      dsimp [f]
      rw [Real.exp_log (htpos x),hx]
    have hfeq : f x = Real.log (max δ (μ.rnDeriv m x).toReal) := by dsimp [f]; rw [hx]
    rw [hfexp,hfeq]
    linarith
  have H := integral_mono_ae hlog (((hrf.sub he).add hr).add (integrable_const δ)) hpoint
  simp only [Pi.add_apply,Pi.sub_apply] at H
  rw [integral_add (f := fun x => (μ.rnDeriv m x).toReal*f x-Real.exp (f x)+(μ.rnDeriv m x).toReal)
      ((hrf.sub he).add hr) (integrable_const δ),
    integral_add (f := fun x => (μ.rnDeriv m x).toReal*f x-Real.exp (f x)) (hrf.sub he) hr,
    integral_sub hrf he,integral_toReal_rnDeriv_mul (f := f) hμ.1,Measure.integral_toReal_rnDeriv hμ.1,
    ← entropyReal_eq_integral_density hμ.1,integral_const,smul_eq_mul] at H
  obtain ⟨g,hg⟩ := exists_continuous_fenchel_approx (m := m) (μ := μ) hf hfA hM hfM (half_pos hε)
  refine ⟨g,?_⟩
  have hδeq : δ*(4*(1+m.real univ)) = ε := div_mul_cancel₀ ε (by positivity)
  have hδerr : m.real univ*δ ≤ ε/4 := by nlinarith
  linarith

lemma entropyReal_le_iff_continuous_support {B : ℝ≥0∞} (hB : B ≠ ∞)
    (hd : μ ≤ B • m) {a : ℝ} :
    entropyReal m μ ≤ a ↔ ∀ g : X →ᵇ ℝ,
      (∫ x, g x ∂μ) - (∫ x, Real.exp (g x) ∂m) + μ.real univ ≤ a := by
  constructor
  · intro ha g
    exact (entropyReal_fenchel (finiteEntropy_of_bounded_density hB hd) g).trans ha
  · intro ha
    apply le_of_forall_pos_le_add
    intro ε hε
    obtain ⟨g,hg⟩ := entropyReal_continuous_support hB hd hε
    exact hg.trans (by linarith [ha g])

end WeakHessian

end
end InlinedFile0

end OAI
end

section
-- module Solutions.OAIQ52_WH.WeakHessian_Entropy_ClosedEntropyAlong
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile0
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

noncomputable section
open scoped ENNReal NNReal Topology BoundedContinuousFunction CompactlySupported
open scoped ENNReal NNReal Topology BoundedContinuousFunction
open scoped NNReal
open MeasureTheory Set Filter
open scoped Topology NNReal ENNReal
open scoped ENNReal NNReal Topology InnerProductSpace
open Set Filter Bornology
open MeasureTheory
open scoped ENNReal InnerProductSpace ComplexConjugate
open scoped Topology ENNReal NNReal
open Set
open Set MeasureTheory CompactlySupported CompactlySupportedContinuousMap
open scoped Topology ENNReal NNReal InnerProductSpace
open Set MeasureTheory Filter
open Set Filter MeasureTheory Topology TopologicalSpace
open scoped ENNReal NNReal
open Filter
open Set Filter MeasureTheory InformationTheory
open Set Filter
open scoped Topology
open Set MeasureTheory ProbabilityTheory
open scoped ENNReal MeasureTheory ProbabilityTheory
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

attribute [local instance] Classical.propDecidable
open Set Filter Topology Bornology
open scoped InnerProductSpace
open scoped BoundedContinuousFunction
open Set Filter Topology

namespace WeakHessian
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology BoundedContinuousFunction

universe u v
variable {X : Type u} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
variable [SecondCountableTopology X]
variable {m : Measure X} [IsFiniteMeasure m]

lemma isClosed_entropy_le_along {T : Type v} [TopologicalSpace T]
    (μ : T → ProbabilityMeasure X) (hμ : Continuous μ)
    {B : ℝ≥0∞} (hB : B ≠ ∞) (hd : ∀ t, (μ t:Measure X) ≤ B • m)
    (a : T → ℝ) (ha : Continuous a) :
    IsClosed {t | entropyReal m (μ t:Measure X) ≤ a t} := by
  have he : {t | entropyReal m (μ t:Measure X) ≤ a t} =
      ⋂ g : X →ᵇ ℝ, {t | (∫ x, g x ∂(μ t:Measure X))-(∫ x, Real.exp (g x) ∂m)+1 ≤ a t} := by
    ext t
    simp only [mem_ofPred_eq,mem_iInter]
    have H := entropyReal_le_iff_continuous_support hB (hd t) (a := a t)
    simpa only [Measure.real,measure_univ,ENNReal.toReal_one] using H
  rw [he]
  apply isClosed_iInter
  intro g
  apply isClosed_le ?_ ha
  exact (((ProbabilityMeasure.continuous_integral_boundedContinuousFunction g).comp hμ).sub continuous_const).add continuous_const

end WeakHessian

end
end InlinedFile0

end OAI
end

section
-- module Solutions.OAIQ52_WH.WeakHessian_Transport_OptimalPlansShort
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile0
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

noncomputable section
open scoped ENNReal NNReal Topology BoundedContinuousFunction CompactlySupported
open scoped ENNReal NNReal Topology BoundedContinuousFunction
open scoped NNReal
open MeasureTheory Set Filter
open scoped Topology NNReal ENNReal
open scoped ENNReal NNReal Topology InnerProductSpace
open Set Filter Bornology
open MeasureTheory
open scoped ENNReal InnerProductSpace ComplexConjugate
open scoped Topology ENNReal NNReal
open Set
open Set MeasureTheory CompactlySupported CompactlySupportedContinuousMap
open scoped Topology ENNReal NNReal InnerProductSpace
open Set MeasureTheory Filter
open Set Filter MeasureTheory Topology TopologicalSpace
open scoped ENNReal NNReal
open Filter
open Set Filter MeasureTheory InformationTheory
open Set Filter
open scoped Topology
open Set MeasureTheory ProbabilityTheory
open scoped ENNReal MeasureTheory ProbabilityTheory
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

attribute [local instance] Classical.propDecidable
open Set Filter Topology Bornology
open scoped InnerProductSpace
open scoped BoundedContinuousFunction
open Set Filter Topology

namespace WeakHessian
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology

variable {X : Type*} [MetricSpace X]

variable [MeasurableSpace X] [BorelSpace X]

lemma optimalPlansShort_of_ball {μ₀ μ₁ : Measure X} (o : X) (R : ℝ≥0)
    (hb₀ : μ₀ (Metric.closedBall o R)ᶜ = 0) (hb₁ : μ₁ (Metric.closedBall o R)ᶜ = 0) :
    OptimalPlansShort μ₀ μ₁ (2*R) := by
  intro π hp hg hopt
  let := hp
  let : IsProbabilityMeasure μ₀ := by rw [← hopt.1.interpolation_endpoints.1]; exact interpolation_probability π _
  let : IsProbabilityMeasure μ₁ := by rw [← hopt.1.interpolation_endpoints.2]; exact interpolation_probability π _
  have H := optimalPlan_supported_tube (μ₀ := ⟨μ₀,(by first | infer_instance | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability))⟩) (μ₁ := ⟨μ₁,(by first | infer_instance | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability))⟩)
    (⟨π,hp⟩ : ProbabilityMeasure (Curve X)) hg hopt.1 hb₀ hb₁
  exact (ae_iff.mpr H).mono fun _ h => boundedEndpointTube_length_le h

end WeakHessian

end
end InlinedFile0

end OAI
end

section
-- module Solutions.OAIQ52_WH.WeakHessian_Entropy_EntropyCell
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile0
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

noncomputable section
open scoped ENNReal NNReal Topology BoundedContinuousFunction CompactlySupported
open scoped ENNReal NNReal Topology BoundedContinuousFunction
open scoped NNReal
open MeasureTheory Set Filter
open scoped Topology NNReal ENNReal
open scoped ENNReal NNReal Topology InnerProductSpace
open Set Filter Bornology
open MeasureTheory
open scoped ENNReal InnerProductSpace ComplexConjugate
open scoped Topology ENNReal NNReal
open Set
open Set MeasureTheory CompactlySupported CompactlySupportedContinuousMap
open scoped Topology ENNReal NNReal InnerProductSpace
open Set MeasureTheory Filter
open Set Filter MeasureTheory Topology TopologicalSpace
open scoped ENNReal NNReal
open Filter
open Set Filter MeasureTheory InformationTheory
open Set Filter
open scoped Topology
open Set MeasureTheory ProbabilityTheory
open scoped ENNReal MeasureTheory ProbabilityTheory
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

attribute [local instance] Classical.propDecidable
open Set Filter Topology Bornology
open scoped InnerProductSpace
open scoped BoundedContinuousFunction
open Set Filter Topology

namespace WeakHessian
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology

universe u
variable {X : Type u} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
variable [SecondCountableTopology X]

lemma optimal_planEnergy_eq {μ₀ μ₁ : Measure X} {π η : Measure (Curve X)}
    (hπ : IsOptimalCoupling (endpointCoupling π) μ₀ μ₁)
    (hη : IsOptimalCoupling (endpointCoupling η) μ₀ μ₁)
    (hIπ : Integrable (fun γ => dist (γ timeZero) (γ timeOne)^2) π)
    (hIη : Integrable (fun γ => dist (γ timeZero) (γ timeOne)^2) η) :
    planEnergy π = planEnergy η := by
  apply (ENNReal.ofReal_eq_ofReal_iff (planEnergy_nonneg π) (planEnergy_nonneg η)).mp
  rw [← planCost_eq_ofReal_energy hIπ,← planCost_eq_ofReal_energy hIη]
  exact le_antisymm (hπ.2 _ hη.1) (hη.2 _ hπ.1)

variable {m : Measure X} {K N : ℝ}

namespace EntropyCell

omit [BorelSpace X] [SecondCountableTopology X] in
lemma uniformCap_finite (c : EntropyCell m K N) : c.uniformCap ≠ ∞ :=
  ENNReal.mul_ne_top c.cap_finite ENNReal.ofReal_ne_top
omit [BorelSpace X] [SecondCountableTopology X] in
lemma cap_le_uniformCap (env : CDEnvironment m K N) (c : EntropyCell m K N) : c.cap ≤ c.uniformCap := by
  have H : (1:ℝ≥0∞) ≤ ENNReal.ofReal (Real.exp (2*compressionRate K N*c.length)) := by
    exact_mod_cast ENNReal.ofReal_le_ofReal (Real.one_le_exp_iff.mpr (mul_nonneg (mul_nonneg (by norm_num) (compressionRate_nonneg (K:=K) env.dimension)) c.length.property))
  simpa only [uniformCap, mul_one] using mul_le_mul' (le_refl c.cap) H

end EntropyCell

namespace CellPlan
lemma energy_eq {c : EntropyCell m K N} (p q : CellPlan c) :
    planEnergy (p.law:Measure (Curve X)) = planEnergy (q.law:Measure (Curve X)) :=
  optimal_planEnergy_eq p.optimal q.optimal p.integrable_energy q.integrable_energy
end CellPlan

variable [ProperSpace X] [SigmaFinite m]

omit [SigmaFinite m]

namespace CellMidpoint
variable {c : EntropyCell m K N}

lemma left_uniformCap (p : CellMidpoint c) (env : CDEnvironment m K N) :
    (p.leftCell env).uniformCap = c.uniformCap := by
  change (c.cap*ENNReal.ofReal (Real.exp (compressionRate K N*c.length)))*
    ENNReal.ofReal (Real.exp (2*compressionRate K N*((c.length:ℝ)/2))) = _
  rw [mul_assoc,← ENNReal.ofReal_mul (Real.exp_pos _).le,← Real.exp_add]
  congr 2
  congr 1
  ring

lemma right_uniformCap (p : CellMidpoint c) (env : CDEnvironment m K N) :
    (p.rightCell env).uniformCap = c.uniformCap := p.left_uniformCap env

end CellMidpoint
end WeakHessian
end
end InlinedFile0

end OAI
end

section
-- module Solutions.OAIQ52_WH.WeakHessian_Geodesics_Join
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile0
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

noncomputable section
open scoped ENNReal NNReal Topology BoundedContinuousFunction CompactlySupported
open scoped ENNReal NNReal Topology BoundedContinuousFunction
open scoped NNReal
open MeasureTheory Set Filter
open scoped Topology NNReal ENNReal
open scoped ENNReal NNReal Topology InnerProductSpace
open Set Filter Bornology
open MeasureTheory
open scoped ENNReal InnerProductSpace ComplexConjugate
open scoped Topology ENNReal NNReal
open Set
open Set MeasureTheory CompactlySupported CompactlySupportedContinuousMap
open scoped Topology ENNReal NNReal InnerProductSpace
open Set MeasureTheory Filter
open Set Filter MeasureTheory Topology TopologicalSpace
open scoped ENNReal NNReal
open Filter
open Set Filter MeasureTheory InformationTheory
open Set Filter
open scoped Topology
open Set MeasureTheory ProbabilityTheory
open scoped ENNReal MeasureTheory ProbabilityTheory
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

attribute [local instance] Classical.propDecidable
open Set Filter Topology Bornology
open scoped InnerProductSpace
open scoped BoundedContinuousFunction
open Set Filter Topology

namespace WeakHessian
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology

universe u
variable {X : Type u} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
variable [SecondCountableTopology X] [ProperSpace X]
variable {m : Measure X} [SigmaFinite m] {K N : ℝ}

namespace CellMidpoint
variable {c : EntropyCell m K N} (p : CellMidpoint c) (env : CDEnvironment m K N)

lemma left_energy (l : CellPlan (p.leftCell env)) :
    planEnergy (l.law:Measure (Curve X)) = planEnergy (p.law:Measure (Curve X))/4 := by
  let r := (env.midpoint (p.rightCell env)).toCellPlan
  have H := (Classical.choose_spec (p.exists_join env l r)).2.2.1
  change ((p.join env l r).law:Measure (Curve X)).map halfCurve = (l.law:Measure (Curve X)) at H
  rw [← H,planEnergy_half (p.join env l r).geodesic]
  rw [(p.join env l r).energy_eq p.toCellPlan]

lemma right_energy (r : CellPlan (p.rightCell env)) :
    planEnergy (r.law:Measure (Curve X)) = planEnergy (p.law:Measure (Curve X))/4 := by
  let l := (env.midpoint (p.leftCell env)).toCellPlan
  have H := (Classical.choose_spec (p.exists_join env l r)).2.2.2
  change ((p.join env l r).law:Measure (Curve X)).map rightCurve = (r.law:Measure (Curve X)) at H
  rw [← H,planEnergy_right (p.join env l r).geodesic]
  rw [(p.join env l r).energy_eq p.toCellPlan]

end CellMidpoint

namespace CDEnvironment
variable (env : CDEnvironment m K N)

lemma build_dominated (n : ℕ) (c : EntropyCell m K N) (t : Time) (ht : t ∈ dyadicTimes n) :
    interpolation ((env.build n c).law:Measure (Curve X)) t ≤ c.uniformCap • m := by
  induction n generalizing c t with
  | zero =>
    rcases ht with rfl | ht
    · rw [(env.build 0 c).optimal.1.interpolation_endpoints.1]
      exact dominated_mono_constant c.left_dominated (c.cap_le_uniformCap env)
    · have H : t = timeOne := ht
      rw [H,(env.build 0 c).optimal.1.interpolation_endpoints.2]
      exact dominated_mono_constant c.right_dominated (c.cap_le_uniformCap env)
  | succ n ih =>
    rcases ht with ⟨s,hs,rfl⟩ | ⟨s,hs,rfl⟩
    · rw [env.build_half,← (env.midpoint c).left_uniformCap env]
      exact ih _ s hs
    · rw [env.build_right,← (env.midpoint c).right_uniformCap env]
      exact ih _ s hs

lemma entropy_chord_half {A B M K E s : ℝ} (hM : M ≤ (A+B)/2-K/8*E) (hs : 0 ≤ s) :
    (1-s)*A+s*M-K/2*(s*(1-s))*(E/4) ≤
      (1-s/2)*A+(s/2)*B-K/2*((s/2)*(1-s/2))*E := by
  calc
    _ ≤ (1-s)*A+s*((A+B)/2-K/8*E)-K/2*(s*(1-s))*(E/4) := by
      have H := mul_le_mul_of_nonneg_left hM hs
      linarith only [H]
    _ = _ := by ring

lemma entropy_chord_right {A B M K E s : ℝ} (hM : M ≤ (A+B)/2-K/8*E) (hs : s ≤ 1) :
    (1-s)*M+s*B-K/2*(s*(1-s))*(E/4) ≤
      (1-(s+1)/2)*A+((s+1)/2)*B-K/2*(((s+1)/2)*(1-(s+1)/2))*E := by
  calc
    _ ≤ (1-s)*((A+B)/2-K/8*E)+s*B-K/2*(s*(1-s))*(E/4) := by
      have H := mul_le_mul_of_nonneg_left hM (sub_nonneg.mpr hs)
      linarith only [H]
    _ = _ := by ring

lemma build_entropy_bound (n : ℕ) (c : EntropyCell m K N) (t : Time) (ht : t ∈ dyadicTimes n) :
    entropyReal m (interpolation ((env.build n c).law:Measure (Curve X)) t) ≤
      (1-(t:ℝ))*entropyReal m (c.leftLaw:Measure X)+(t:ℝ)*entropyReal m (c.rightLaw:Measure X) -
        K/2*((t:ℝ)*(1-(t:ℝ)))*planEnergy ((env.build n c).law:Measure (Curve X)) := by
  induction n generalizing c t with
  | zero =>
    rcases ht with rfl | ht
    · rw [(env.build 0 c).optimal.1.interpolation_endpoints.1]
      simp only [timeZero,sub_zero,one_mul,zero_mul,mul_zero,add_zero,le_refl]
    · have H : t = timeOne := ht
      rw [H,(env.build 0 c).optimal.1.interpolation_endpoints.2]
      simp only [timeOne,sub_self,zero_mul,one_mul,zero_add,mul_zero,sub_zero,le_refl]
  | succ n ih =>
    have hE := (env.build (n+1) c).energy_eq (env.midpoint c).toCellPlan
    rw [hE]
    rcases ht with ⟨s,hs,rfl⟩ | ⟨s,hs,rfl⟩
    · rw [env.build_half]
      apply (ih ((env.midpoint c).leftCell env) s hs).trans
      rw [(env.midpoint c).left_energy env]
      exact entropy_chord_half (env.midpoint c).entropy_bound s.2.1
    · rw [env.build_right]
      apply (ih ((env.midpoint c).rightCell env) s hs).trans
      rw [(env.midpoint c).right_energy env]
      exact entropy_chord_right (env.midpoint c).entropy_bound s.2.2

end CDEnvironment
end WeakHessian

end
end InlinedFile0

end OAI
end

section
-- module Solutions.OAIQ52_WH.WeakHessian_LocalBounds_Law
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile0
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

noncomputable section
open scoped ENNReal NNReal Topology BoundedContinuousFunction CompactlySupported
open scoped ENNReal NNReal Topology BoundedContinuousFunction
open scoped NNReal
open MeasureTheory Set Filter
open scoped Topology NNReal ENNReal
open scoped ENNReal NNReal Topology InnerProductSpace
open Set Filter Bornology
open MeasureTheory
open scoped ENNReal InnerProductSpace ComplexConjugate
open scoped Topology ENNReal NNReal
open Set
open Set MeasureTheory CompactlySupported CompactlySupportedContinuousMap
open scoped Topology ENNReal NNReal InnerProductSpace
open Set MeasureTheory Filter
open Set Filter MeasureTheory Topology TopologicalSpace
open scoped ENNReal NNReal
open Filter
open Set Filter MeasureTheory InformationTheory
open Set Filter
open scoped Topology
open Set MeasureTheory ProbabilityTheory
open scoped ENNReal MeasureTheory ProbabilityTheory
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

attribute [local instance] Classical.propDecidable
open Set Filter Topology Bornology
open scoped InnerProductSpace
open scoped BoundedContinuousFunction
open Set Filter Topology

namespace WeakHessian
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology

universe u
variable {X : Type u} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
variable [SecondCountableTopology X] [ProperSpace X]
variable {m : Measure X} [SigmaFinite m] {K N : ℝ}

omit [SecondCountableTopology X] [ProperSpace X] in
lemma continuous_lawAt_time (π : ProbabilityMeasure (Curve X)) : Continuous (lawAt π) := by
  apply ProbabilityMeasure.continuous_iff_forall_continuous_integral.mpr
  intro f
  have he (t : Time) : (∫ x, f x ∂(lawAt π t:Measure X)) = ∫ γ, f (γ t) ∂(π:Measure (Curve X)) :=
    integral_map (continuous_eval_const t).measurable.aemeasurable f.continuous.aestronglyMeasurable
  simp_rw [he]
  apply continuous_of_dominated (bound := fun _ => ‖f‖)
  · intro t; exact (f.continuous.comp (continuous_eval_const t)).aestronglyMeasurable
  · intro t; exact ae_of_all _ fun γ => f.norm_coe_le_norm (γ t)
  · exact integrable_const ‖f‖
  · exact ae_of_all _ fun γ => f.continuous.comp γ.continuous

omit [MeasurableSpace X] [BorelSpace X] [SecondCountableTopology X] [ProperSpace X] in
lemma IsGeodesic.speed_energy_le {γ : Curve X} (hγ : IsGeodesic γ) :
    (∫⁻ t in Icc (0:ℝ) 1, (metricSpeed γ t)^2) ≤ ENNReal.ofReal (dist (γ timeZero) (γ timeOne)^2) := by
  calc
    _ ≤ ∫⁻ _t in Icc (0:ℝ) 1, (ENNReal.ofReal (dist (γ timeZero) (γ timeOne)))^2 := by
      apply lintegral_mono_ae
      exact hγ.squareControl.metricSpeed_le.mono fun t ht => pow_le_pow_left' ht 2
    _ = _ := by simp only [lintegral_const,Measure.restrict_apply_univ,Real.volume_Icc,
        sub_zero,ENNReal.ofReal_one,mul_one,ENNReal.ofReal_pow dist_nonneg]

namespace CDEnvironment
variable (env : CDEnvironment m K N)

lemma limitPlan_dyadic (c : EntropyCell m K N) (n : ℕ) (t : Time) (ht : t ∈ dyadicTimes n) :
    interpolation ((env.limitPlan c).law:Measure (Curve X)) t =
      interpolation ((env.build n c).law:Measure (Curve X)) t :=
  Classical.choose_spec (env.exists_stable_plan c) n t ht

lemma limitPlan_entropy_bound_dyadic (c : EntropyCell m K N) (n : ℕ) (t : Time) (ht : t ∈ dyadicTimes n) :
    entropyReal m (interpolation ((env.limitPlan c).law:Measure (Curve X)) t) ≤
      (1-(t:ℝ))*entropyReal m (c.leftLaw:Measure X)+(t:ℝ)*entropyReal m (c.rightLaw:Measure X) -
        K/2*((t:ℝ)*(1-(t:ℝ)))*planEnergy ((env.limitPlan c).law:Measure (Curve X)) := by
  rw [env.limitPlan_dyadic c n t ht,(env.limitPlan c).energy_eq (env.build n c)]
  exact env.build_entropy_bound n c t ht

lemma limitPlan_dominated_dyadic (c : EntropyCell m K N) (n : ℕ) (t : Time) (ht : t ∈ dyadicTimes n) :
    interpolation ((env.limitPlan c).law:Measure (Curve X)) t ≤ c.uniformCap • m := by
  rw [env.limitPlan_dyadic c n t ht]
  exact env.build_dominated n c t ht

lemma limitPlan_dominated (c : EntropyCell m K N) (t : Time) :
    interpolation ((env.limitPlan c).law:Measure (Curve X)) t ≤ c.uniformCap • m := by
  let Q := Metric.closedBall c.center (3*(c.radius:ℝ))
  let : IsFiniteMeasure (m.restrict Q) := ⟨by
    simpa only [Measure.restrict_apply_univ] using env.finite_bounded Q Metric.isBounded_closedBall⟩
  have hnu : IsFiniteMeasure (c.uniformCap • m.restrict Q) := ⟨by
    rw [Measure.smul_apply,smul_eq_mul]
    exact ENNReal.mul_lt_top c.uniformCap_finite.lt_top (measure_lt_top _ _)⟩
  let := hnu
  have hclosed : IsClosed {s : Time |
      (lawAt (env.limitPlan c).law s:Measure X) ≤ c.uniformCap • m.restrict Q} :=
    (isClosed_probability_dominated _).preimage (continuous_lawAt_time _)
  have hdyadic : (⋃ n, dyadicTimes n) ⊆ {s : Time |
      (lawAt (env.limitPlan c).law s:Measure X) ≤ c.uniformCap • m.restrict Q} := by
    intro s hs
    obtain ⟨n,hn⟩ := mem_iUnion.mp hs
    have hd := env.limitPlan_dominated_dyadic c n s hn
    have hsupport : interpolation ((env.limitPlan c).law:Measure (Curve X)) s Qᶜ = 0 :=
      geodesic_plan_supported_ball _ (env.limitPlan c).geodesic c.center c.radius
        (by rw [(env.limitPlan c).optimal.1.interpolation_endpoints.1]; exact c.left_supported)
        (by rw [(env.limitPlan c).optimal.1.interpolation_endpoints.2]; exact c.right_supported) s
    have H := Measure.restrict_mono_measure hd Q
    rwa [Measure.restrict_eq_self_of_ae_mem (ae_iff.mpr hsupport),Measure.restrict_smul] at H
  have H : (lawAt (env.limitPlan c).law t:Measure X) ≤ c.uniformCap • m.restrict Q :=
    (closure_minimal hdyadic hclosed) (dense_dyadicTimes t)
  exact H.trans (smul_le_smul_left _ Measure.restrict_le_self)

lemma limitPlan_supported (c : EntropyCell m K N) (t : Time) :
    interpolation ((env.limitPlan c).law:Measure (Curve X)) t (Metric.closedBall c.center (3*(c.radius:ℝ)))ᶜ = 0 :=
  geodesic_plan_supported_ball _ (env.limitPlan c).geodesic c.center c.radius
    (by rw [(env.limitPlan c).optimal.1.interpolation_endpoints.1]; exact c.left_supported)
    (by rw [(env.limitPlan c).optimal.1.interpolation_endpoints.2]; exact c.right_supported) t

lemma limitPlan_finite_entropy (c : EntropyCell m K N) (t : Time) :
    FiniteEntropy m (interpolation ((env.limitPlan c).law:Measure (Curve X)) t) := by
  let Q := Metric.closedBall c.center (3*(c.radius:ℝ))
  let : IsFiniteMeasure (m.restrict Q) := ⟨by
    simpa only [Measure.restrict_apply_univ] using env.finite_bounded Q Metric.isBounded_closedBall⟩
  let : IsProbabilityMeasure (interpolation ((env.limitPlan c).law:Measure (Curve X)) t) :=
    interpolation_probability _ _
  have hs : ∀ᵐ x ∂interpolation ((env.limitPlan c).law:Measure (Curve X)) t, x ∈ Q :=
    ae_iff.mpr (env.limitPlan_supported c t)
  apply (finiteEntropy_restrict_reference_iff Metric.isClosed_closedBall.measurableSet hs).mp
  apply finiteEntropy_of_bounded_density c.uniformCap_finite
  have H := Measure.restrict_mono_measure (env.limitPlan_dominated c t) Q
  rwa [Measure.restrict_eq_self_of_ae_mem hs,Measure.restrict_smul] at H

lemma limitPlan_boundedTracks (c : EntropyCell m K N) :
    BoundedTracks ((env.limitPlan c).law:Measure (Curve X)) := by
  refine ⟨c.center,3*(c.radius:ℝ)+1,by positivity,?_⟩
  have H := optimalPlan_supported_tube (env.limitPlan c).law (env.limitPlan c).geodesic
    (env.limitPlan c).optimal.1 c.left_supported c.right_supported
  filter_upwards [ae_iff.mpr H] with γ hγ
  intro t
  exact (boundedEndpointTube_range hγ t).trans (by linarith)

lemma limitPlan_isTestPlan (c : EntropyCell m K N) :
    IsTestPlan m ((env.limitPlan c).law:Measure (Curve X)) := by
  refine ⟨(by first | infer_instance | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)),⟨c.uniformCap.toNNReal,?_⟩,?_,?_⟩
  · intro t
    rw [ENNReal.coe_toNNReal c.uniformCap_finite]
    exact env.limitPlan_dominated c t
  · exact (env.limitPlan c).geodesic.mono fun γ hγ => hγ.squareControl.isAC2
  · have hB : (∫⁻ γ, ∫⁻ t in Icc (0:ℝ) 1, (metricSpeed γ t)^2
        ∂volume ∂((env.limitPlan c).law:Measure (Curve X))) ≤ ENNReal.ofReal ((c.length:ℝ)^2) := by
      calc
        _ ≤ ∫⁻ _γ, ENNReal.ofReal ((c.length:ℝ)^2) ∂((env.limitPlan c).law:Measure (Curve X)) := by
          apply lintegral_mono_ae
          filter_upwards [(env.limitPlan c).geodesic,
            c.short _ inferInstance (env.limitPlan c).geodesic (env.limitPlan c).optimal] with γ hγ hlen
          exact hγ.speed_energy_le.trans (ENNReal.ofReal_le_ofReal (pow_le_pow_left₀ dist_nonneg hlen 2))
        _ = _ := by simp only [lintegral_const,measure_univ,mul_one]
    exact hB.trans_lt ENNReal.ofReal_lt_top

end CDEnvironment
end WeakHessian

end
end InlinedFile0

end OAI
end

section
-- module Solutions.OAIQ52_WH.WeakHessian_Transport_LimitPlanEntropyBound
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile0
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

noncomputable section
open scoped ENNReal NNReal Topology BoundedContinuousFunction CompactlySupported
open scoped ENNReal NNReal Topology BoundedContinuousFunction
open scoped NNReal
open MeasureTheory Set Filter
open scoped Topology NNReal ENNReal
open scoped ENNReal NNReal Topology InnerProductSpace
open Set Filter Bornology
open MeasureTheory
open scoped ENNReal InnerProductSpace ComplexConjugate
open scoped Topology ENNReal NNReal
open Set
open Set MeasureTheory CompactlySupported CompactlySupportedContinuousMap
open scoped Topology ENNReal NNReal InnerProductSpace
open Set MeasureTheory Filter
open Set Filter MeasureTheory Topology TopologicalSpace
open scoped ENNReal NNReal
open Filter
open Set Filter MeasureTheory InformationTheory
open Set Filter
open scoped Topology
open Set MeasureTheory ProbabilityTheory
open scoped ENNReal MeasureTheory ProbabilityTheory
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

attribute [local instance] Classical.propDecidable
open Set Filter Topology Bornology
open scoped InnerProductSpace
open scoped BoundedContinuousFunction
open Set Filter Topology

namespace WeakHessian
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology

universe u
variable {X : Type u} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
variable [SecondCountableTopology X] [ProperSpace X]
variable {m : Measure X} [SigmaFinite m] {K N : ℝ}

namespace CDEnvironment
variable (env : CDEnvironment m K N)

lemma limitPlan_entropy_bound (c : EntropyCell m K N) (t : Time) :
    entropyReal m (interpolation ((env.limitPlan c).law:Measure (Curve X)) t) ≤
      (1-(t:ℝ))*entropyReal m (c.leftLaw:Measure X)+(t:ℝ)*entropyReal m (c.rightLaw:Measure X) -
        K/2*((t:ℝ)*(1-(t:ℝ)))*planEnergy ((env.limitPlan c).law:Measure (Curve X)) := by
  let Q := Metric.closedBall c.center (3*(c.radius:ℝ))
  let : IsFiniteMeasure (m.restrict Q) := ⟨by
    simpa only [Measure.restrict_apply_univ] using env.finite_bounded Q Metric.isBounded_closedBall⟩
  let p := (env.limitPlan c).law
  have hs (s : Time) : ∀ᵐ x ∂(lawAt p s:Measure X), x ∈ Q :=
    ae_iff.mpr (env.limitPlan_supported c s)
  have hd (s : Time) : (lawAt p s:Measure X) ≤ c.uniformCap • m.restrict Q := by
    have H := Measure.restrict_mono_measure (env.limitPlan_dominated c s) Q
    change (lawAt p s:Measure X).restrict Q ≤ (c.uniformCap • m).restrict Q at H
    rwa [Measure.restrict_eq_self_of_ae_mem (hs s),Measure.restrict_smul] at H
  have he (s : Time) : entropyReal (m.restrict Q) (lawAt p s:Measure X) =
      entropyReal m (lawAt p s:Measure X) :=
    entropyReal_restrict_reference Metric.isClosed_closedBall.measurableSet
      (env.limitPlan_finite_entropy c s).1 (hs s)
  let a : Time → ℝ := fun s =>
      (1-(s:ℝ))*entropyReal m (c.leftLaw:Measure X)+(s:ℝ)*entropyReal m (c.rightLaw:Measure X) -
        K/2*((s:ℝ)*(1-(s:ℝ)))*planEnergy (p:Measure (Curve X))
  have ha : Continuous a := by dsimp [a]; fun_prop
  have hc : IsClosed {s | entropyReal m (lawAt p s:Measure X) ≤ a s} := by
    simp_rw [← he]
    exact isClosed_entropy_le_along (lawAt p) (continuous_lawAt_time p) c.uniformCap_finite hd a ha
  have hdy : (⋃ n, dyadicTimes n) ⊆ {s | entropyReal m (lawAt p s:Measure X) ≤ a s} := by
    intro s hs
    obtain ⟨n,hn⟩ := mem_iUnion.mp hs
    exact env.limitPlan_entropy_bound_dyadic c n s hn
  exact (closure_minimal hdy hc) (dense_dyadicTimes t)

end CDEnvironment
end WeakHessian

end
end InlinedFile0

end OAI
end

section
-- module Solutions.OAIQ52_WH.WeakHessian_Entropy_FiniteEntropyBoundedSupported
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology


open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

noncomputable section

attribute [local instance] Classical.propDecidable
open Set Filter Topology Bornology
open scoped InnerProductSpace


open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology


attribute [local instance] Classical.propDecidable
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology


open Set
open scoped NNReal


open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology


open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology


attribute [local instance] Classical.propDecidable
open Set Filter Topology Bornology
open scoped InnerProductSpace


open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology


attribute [local instance] Classical.propDecidable
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology


open Set
open scoped NNReal


open Set Filter
open scoped ENNReal NNReal Topology InnerProductSpace


open Set Filter Bornology
open scoped Topology


open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology


open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology


open Set Filter
open scoped Topology ENNReal NNReal


open Set Filter
open scoped ENNReal NNReal Topology InnerProductSpace


open Set Filter Bornology
open scoped Topology


open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology


open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology


open Set Filter
open scoped Topology ENNReal NNReal


open Set


open Set MeasureTheory CompactlySupported CompactlySupportedContinuousMap
open scoped ENNReal NNReal Topology


open Set Filter
open scoped Topology ENNReal NNReal


open Set


open Set MeasureTheory CompactlySupported CompactlySupportedContinuousMap
open scoped ENNReal NNReal Topology


open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology BoundedContinuousFunction CompactlySupported


open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology BoundedContinuousFunction


open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal InnerProductSpace


open Set Filter
open scoped ENNReal NNReal Topology InnerProductSpace


open Set Filter Bornology
open scoped Topology


open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology


open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology


open Set Filter
open scoped Topology ENNReal NNReal


open Set Filter
open scoped ENNReal NNReal Topology InnerProductSpace


open Set Filter Bornology
open scoped Topology


open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology


open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology


open Set Filter
open scoped Topology ENNReal NNReal


open Set Filter
open scoped ENNReal NNReal Topology InnerProductSpace


open Set Filter Bornology
open scoped Topology


open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology


attribute [local instance] Classical.propDecidable
open Set Filter Topology Bornology
open scoped InnerProductSpace


open scoped InnerProductSpace
open scoped BoundedContinuousFunction
open Set MeasureTheory Filter
open scoped ENNReal NNReal


open Set Filter MeasureTheory Topology TopologicalSpace
open scoped ENNReal NNReal


open Set MeasureTheory ProbabilityTheory
open scoped ENNReal MeasureTheory ProbabilityTheory


open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology


attribute [local instance] Classical.propDecidable
open Set Filter Topology Bornology
open scoped InnerProductSpace


open scoped InnerProductSpace
open scoped BoundedContinuousFunction
open Set Filter MeasureTheory Topology TopologicalSpace
open scoped ENNReal NNReal


open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology


attribute [local instance] Classical.propDecidable
open Set Filter Topology Bornology
open scoped InnerProductSpace


open scoped InnerProductSpace
open scoped BoundedContinuousFunction
open Set MeasureTheory Filter
open scoped ENNReal NNReal


open Set Filter MeasureTheory Topology TopologicalSpace
open scoped ENNReal NNReal


open Set MeasureTheory ProbabilityTheory
open scoped ENNReal MeasureTheory ProbabilityTheory


open Set Filter
open scoped ENNReal NNReal Topology InnerProductSpace


open Set Filter Bornology
open scoped Topology


open MeasureTheory
open scoped ENNReal InnerProductSpace ComplexConjugate


open Set Filter
open scoped Topology


open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology


open Set Filter
open scoped Topology ENNReal NNReal


open Set


open Set MeasureTheory CompactlySupported CompactlySupportedContinuousMap
open scoped ENNReal NNReal Topology


open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal InnerProductSpace


open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology


attribute [local instance] Classical.propDecidable
open Set Filter Topology Bornology
open scoped InnerProductSpace


open scoped InnerProductSpace
open scoped BoundedContinuousFunction
open Set MeasureTheory Filter
open scoped ENNReal NNReal


open Set Filter MeasureTheory Topology TopologicalSpace
open scoped ENNReal NNReal


open Set MeasureTheory ProbabilityTheory
open scoped ENNReal MeasureTheory ProbabilityTheory


open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology


attribute [local instance] Classical.propDecidable
open Set Filter Topology Bornology
open scoped InnerProductSpace


open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology


attribute [local instance] Classical.propDecidable
open Set Filter Topology Bornology
open scoped InnerProductSpace


open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology


attribute [local instance] Classical.propDecidable
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology


open Set
open scoped NNReal


open Set Filter
open scoped ENNReal NNReal Topology InnerProductSpace


open Set Filter Bornology
open scoped Topology


open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology


open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology


open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology


attribute [local instance] Classical.propDecidable
open Set Filter Topology Bornology
open scoped InnerProductSpace


open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology


attribute [local instance] Classical.propDecidable
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology


attribute [local instance] Classical.propDecidable
open Set Filter Topology Bornology
open scoped InnerProductSpace


open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology


attribute [local instance] Classical.propDecidable
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology


open Set
open scoped NNReal


open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology



open MeasureTheory Set Filter
open scoped Topology ENNReal NNReal



open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology


open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology


open MeasureTheory Set Filter
open scoped Topology NNReal ENNReal



open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology


attribute [local instance] Classical.propDecidable
open Set Filter Topology Bornology
open scoped InnerProductSpace


open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology


attribute [local instance] Classical.propDecidable
open Set Filter
open scoped ENNReal NNReal Topology InnerProductSpace


open Set Filter Bornology
open scoped Topology


open MeasureTheory
open scoped ENNReal InnerProductSpace ComplexConjugate


open Set Filter
open scoped Topology


open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology


open Set Filter
open scoped Topology ENNReal NNReal


open Set


open Set MeasureTheory CompactlySupported CompactlySupportedContinuousMap
open scoped ENNReal NNReal Topology


open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal InnerProductSpace


open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology


attribute [local instance] Classical.propDecidable
open Set Filter Topology Bornology
open scoped InnerProductSpace


open scoped InnerProductSpace
open scoped BoundedContinuousFunction
open Set MeasureTheory Filter
open scoped ENNReal NNReal


open Set Filter MeasureTheory Topology TopologicalSpace
open scoped ENNReal NNReal


open Set MeasureTheory ProbabilityTheory
open scoped ENNReal MeasureTheory ProbabilityTheory


open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology


attribute [local instance] Classical.propDecidable
open Set Filter Topology Bornology
open scoped InnerProductSpace


open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology


attribute [local instance] Classical.propDecidable
open Set Filter Topology Bornology
open scoped InnerProductSpace


open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology


attribute [local instance] Classical.propDecidable
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology


attribute [local instance] Classical.propDecidable
open Filter
open scoped Topology
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology


attribute [local instance] Classical.propDecidable
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology


attribute [local instance] Classical.propDecidable



open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology


attribute [local instance] Classical.propDecidable
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology


open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology


attribute [local instance] Classical.propDecidable
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology


attribute [local instance] Classical.propDecidable
open Filter
open scoped Topology
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology


attribute [local instance] Classical.propDecidable
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology


attribute [local instance] Classical.propDecidable



open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology


attribute [local instance] Classical.propDecidable
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology


open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology


attribute [local instance] Classical.propDecidable




























open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology


attribute [local instance] Classical.propDecidable
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology


attribute [local instance] Classical.propDecidable













open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology


attribute [local instance] Classical.propDecidable
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology


open Set Filter MeasureTheory InformationTheory
open scoped Topology


open Set Filter
open scoped Topology


open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology



open Set MeasureTheory ProbabilityTheory
open scoped ENNReal MeasureTheory ProbabilityTheory


open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology


attribute [local instance] Classical.propDecidable
open Set Filter Topology Bornology
open scoped InnerProductSpace


open scoped InnerProductSpace
open scoped BoundedContinuousFunction
open Set Filter Topology














namespace WeakHessian
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology

universe u
variable {X : Type u} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
variable [SecondCountableTopology X] [ProperSpace X]
variable {m : Measure X} [SigmaFinite m] {K N : ℝ}

omit [SecondCountableTopology X] [ProperSpace X] in
lemma finiteEntropy_of_bounded_supported (hf : FiniteOnBoundedSets m)
    (μ : ProbabilityMeasure X) (o : X) (R : ℝ≥0)
    (hs : (μ:Measure X) (Metric.closedBall o R)ᶜ = 0) {C : ℝ≥0∞}
    (hC : C ≠ ∞) (hd : (μ:Measure X) ≤ C • m) : FiniteEntropy m (μ:Measure X) := by
  let Q := Metric.closedBall o (R:ℝ)
  let : IsFiniteMeasure (m.restrict Q) := ⟨by
    simpa only [Measure.restrict_apply_univ] using hf Q Metric.isBounded_closedBall⟩
  have hs' : ∀ᵐ x ∂(μ:Measure X), x ∈ Q := ae_iff.mpr hs
  apply (finiteEntropy_restrict_reference_iff Metric.isClosed_closedBall.measurableSet hs').mp
  apply finiteEntropy_of_bounded_density hC
  have H := Measure.restrict_mono_measure hd Q
  rwa [Measure.restrict_eq_self_of_ae_mem hs',Measure.restrict_smul] at H

theorem CurvatureDimension.exists_entropy_testPlan (hN : 1 < N)
    (hCD : CurvatureDimension m K N) (hf : FiniteOnBoundedSets m)
    (μ₀ μ₁ : ProbabilityMeasure X) (o : X) (R : ℝ≥0)
    (hs₀ : (μ₀:Measure X) (Metric.closedBall o R)ᶜ = 0)
    (hs₁ : (μ₁:Measure X) (Metric.closedBall o R)ᶜ = 0)
    {C : ℝ≥0∞} (hC0 : C ≠ 0) (hCt : C ≠ ∞)
    (h₀ : (μ₀:Measure X) ≤ C • m) (h₁ : (μ₁:Measure X) ≤ C • m) :
    ∃ π : ProbabilityMeasure (Curve X), IsTestPlan m (π:Measure (Curve X)) ∧
      BoundedTracks (π:Measure (Curve X)) ∧
      (∀ᵐ γ ∂(π:Measure (Curve X)), IsGeodesic γ) ∧
      IsOptimalCoupling (endpointCoupling (π:Measure (Curve X))) μ₀ μ₁ ∧
      (∀ t : Time, FiniteEntropy m (interpolation (π:Measure (Curve X)) t)) ∧
      (∀ t : Time,
        entropyReal m (interpolation (π:Measure (Curve X)) t) ≤
          (1-(t:ℝ))*entropyReal m (μ₀:Measure X) +
          (t:ℝ)*entropyReal m (μ₁:Measure X) -
          K/2*(t:ℝ)*(1-(t:ℝ))*planEnergy (π:Measure (Curve X))) ∧
      (∀ t : Time, interpolation (π:Measure (Curve X)) t ≤
        (C*ENNReal.ofReal (Real.exp (4*compressionRate K N*R))) • m) := by
  let env : CDEnvironment m K N := ⟨hN,hCD,hf⟩
  let c : EntropyCell m K N := {
    leftLaw := μ₀, rightLaw := μ₁, center := o, radius := R, length := 2*R,
    cap := C, cap_pos := hC0, cap_finite := hCt,
    left_supported := hs₀, right_supported := hs₁,
    left_dominated := h₀, right_dominated := h₁,
    left_entropy := finiteEntropy_of_bounded_supported hf μ₀ o R hs₀ hCt h₀,
    right_entropy := finiteEntropy_of_bounded_supported hf μ₁ o R hs₁ hCt h₁,
    short := by simpa using optimalPlansShort_of_ball o R hs₀ hs₁ }
  refine ⟨(env.limitPlan c).law,env.limitPlan_isTestPlan c,env.limitPlan_boundedTracks c,
    (env.limitPlan c).geodesic,(env.limitPlan c).optimal,
    env.limitPlan_finite_entropy c,?_,?_⟩
  · intro t
    simpa only [c,mul_assoc] using env.limitPlan_entropy_bound c t
  · intro t
    have h := env.limitPlan_dominated c t
    have hcap : c.uniformCap = C*ENNReal.ofReal (Real.exp (4*compressionRate K N*R)) := by
      dsimp only [EntropyCell.uniformCap,c]
      congr 3
      push_cast
      ring
    rwa [hcap] at h

end WeakHessian

end

end OAI
end

section
-- module Solutions.OAIQ52_WH.WeakHessian_Entropy_StrongEntropyConfinement
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile0
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

noncomputable section
open scoped ENNReal NNReal Topology BoundedContinuousFunction CompactlySupported
open scoped ENNReal NNReal Topology BoundedContinuousFunction
open scoped NNReal
open MeasureTheory Set Filter
open scoped Topology NNReal ENNReal
open scoped ENNReal NNReal Topology InnerProductSpace
open Set Filter Bornology
open MeasureTheory
open scoped ENNReal InnerProductSpace ComplexConjugate
open Set Filter
open scoped Topology ENNReal NNReal
open Set
open Set MeasureTheory CompactlySupported CompactlySupportedContinuousMap
open scoped Topology ENNReal NNReal InnerProductSpace
open scoped BoundedContinuousFunction
open Set MeasureTheory Filter
open Set Filter MeasureTheory Topology TopologicalSpace
open scoped ENNReal NNReal
open Set MeasureTheory ProbabilityTheory
open scoped ENNReal MeasureTheory ProbabilityTheory
open Set Filter Topology Bornology
open scoped InnerProductSpace
open Filter
open scoped Topology
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

attribute [local instance] Classical.propDecidable
namespace WeakHessian
open MeasureTheory Set Filter
open scoped Topology NNReal ENNReal

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] {m : Measure X}
lemma CurvatureDimension.exists_strong_entropy_confinement {K N : ℝ} (hN : 1 < N)
    (hcd : CurvatureDimension m K N) (hfull : FullSupport m) (hfin : FiniteOnBoundedSets m) (o : X) :
    ∃ a : ℝ, 0 < a ∧
      Integrable (fun x => Real.exp (-(a*dist x o))) m ∧
      MemLp (fun x => Real.exp (-(a*dist x o))) 2 m ∧
      MemLp (fun x => (a*dist x o)*Real.exp (-(a*dist x o))) 2 m ∧
      MemLp (fun x => Real.exp (-(a*dist x o/2))) 2 m ∧
      Integrable (fun x => Real.exp (-(a*dist x o/2))) m := by
  let C := N*Real.log 2+8*Real.sqrt (|K|/(N-1))*(N-1)
  let d := |C|+1
  have hd : 0 < d := by dsimp [d]; positivity
  have hCd : C < d := by dsimp [d]; linarith [le_abs_self C]
  have hvol := cd_ball_volume_bound hN hcd hfull hfin o
  have hbase : MemLp (fun x => Real.exp (-(d*dist x o))) 2 m := by
    simpa only [neg_mul] using memLp_exp_neg_dist_of_growth o ENNReal.toReal_nonneg hd.le
      (show C < 2*d by linarith) hvol
  have hbI : Integrable (fun x => Real.exp (-(d*dist x o))) m := by
    simpa only [neg_mul] using integrable_exp_neg_dist_of_growth o ENNReal.toReal_nonneg hd.le hCd hvol
  refine ⟨2*d,by positivity,?_,?_,?_,?_,?_⟩
  · simpa only [neg_mul] using integrable_exp_neg_dist_of_growth o ENNReal.toReal_nonneg
      (show 0 ≤ 2*d by positivity) (show C < 2*d by linarith) hvol
  · simpa only [neg_mul] using memLp_exp_neg_dist_of_growth o ENNReal.toReal_nonneg
      (show 0 ≤ 2*d by positivity) (show C < 2*(2*d) by linarith) hvol
  · apply (hbase.const_mul 2).mono (by fun_prop)
    exact ae_of_all _ fun x => by
      change |(2*d*dist x o)*Real.exp (-(2*d*dist x o))| ≤ |2*Real.exp (-(d*dist x o))|
      rw [abs_of_nonneg (by positivity),abs_of_nonneg (by positivity)]
      have H := (Real.mul_exp_neg_le_exp_neg_one (d*dist x o)).trans
        (show Real.exp (-1) ≤ 1 by rw [Real.exp_le_one_iff]; norm_num)
      have he : (2*d*dist x o)*Real.exp (-(2*d*dist x o)) =
          2*(d*dist x o*Real.exp (-(d*dist x o)))*Real.exp (-(d*dist x o)) := by
        rw [show -(2*d*dist x o) = -(d*dist x o)+(-(d*dist x o)) by ring,Real.exp_add]
        ring
      rw [he]
      nlinarith [Real.exp_pos (-(d*dist x o))]
  · convert! hbase using 1; funext x; congr 1; ring
  · convert! hbI using 1; funext x; congr 1; ring
end WeakHessian

end
end InlinedFile0

end OAI
end

section
-- module Solutions.OAIQ52_WH.WeakHessian_LocalBounds_WeightedEnergySpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile181
noncomputable section
namespace WeakHessian
open Set Filter MeasureTheory WeakHessianFunctional
open scoped Topology ENNReal NNReal InnerProductSpace

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
variable [CompleteSpace X] [ProperSpace X] [TopologicalSpace.SeparableSpace X] {m : Measure X} [SigmaFinite m]

omit [CompleteSpace X] [SigmaFinite m] in
lemma RCD.cheegerEnergy_integral {K N : ℝ} (hrcd : RCD m K N)
    (hfin : FiniteOnBoundedSets m) (o : X) {f : X → ℝ} (hf : Sobolev m f) :
    cheegerEnergy m f = ENNReal.ofReal ((∫ x,(weakGradient m f x)^2 ∂m)/2) := by
  rw [hrcd.1.global_cheegerEnergy_eq_weakGradient hfin o hf,norm_toLp_sq_eq_integral]

omit [SigmaFinite m] in
lemma RCD.weighted_quadraticCheegerEnergy {K N : ℝ} (hrcd : RCD m K N)
    (hfin : FiniteOnBoundedSets m) (o : X) {V : X → ℝ} {B : ℝ} (hB : ∀ x,|V x| ≤ B) :
    QuadraticCheegerEnergy (exponentialMeasure m V) := by
  obtain ⟨hm,hν⟩ := exponentialMeasure_comparable (m := m) hB
  exact quadraticCheegerEnergy_of_comparable hfin hrcd.2
    (fun f hf => hrcd.cheegerEnergy_integral hfin o hf)
    (C := (Real.exp B).toNNReal) (E := (Real.exp B).toNNReal) hm hν

end WeakHessian

end
end InlinedFile181

end OAI
end

section
-- module Solutions.OAIQ52_WH.WeakHessian_Entropy_CompressedDensity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section
noncomputable section
namespace WeakHessian
open Set Filter MeasureTheory WeakHessianTransport
open scoped Topology ENNReal NNReal InnerProductSpace

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
variable {m μ : Measure X} [SigmaFinite m] [IsFiniteMeasure μ]

omit [MetricSpace X] [BorelSpace X] [IsFiniteMeasure μ] in
lemma toReal_rnDeriv_bounded {B : ℝ≥0} (hμ : μ ≤ (B : ℝ≥0∞) • m) :
    ∀ᵐ x ∂m, |(μ.rnDeriv m x).toReal| ≤ B := by
  filter_upwards [rnDeriv_le_of_le_smul hμ] with x hx
  rw [abs_of_nonneg ENNReal.toReal_nonneg]
  exact (ENNReal.toReal_mono ENNReal.coe_ne_top hx).trans_eq (ENNReal.coe_toReal B)

omit [MetricSpace X] [BorelSpace X] in
lemma toReal_rnDeriv_memLp {B : ℝ≥0} (hμ : μ ≤ (B : ℝ≥0∞) • m) :
    MemLp (fun x => (μ.rnDeriv m x).toReal) 2 m := by
  have hm : AEStronglyMeasurable (fun x => (μ.rnDeriv m x).toReal) m :=
    (μ.measurable_rnDeriv m).ennreal_toReal.aestronglyMeasurable
  apply (memLp_two_iff_integrable_sq hm).mpr
  apply ((Measure.integrable_toReal_rnDeriv (μ := μ) (ν := m)).const_mul (B : ℝ)).mono' (hm.pow 2)
  filter_upwards [toReal_rnDeriv_bounded hμ] with x hx
  rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)]
  have hn : 0 ≤ (μ.rnDeriv m x).toReal := ENNReal.toReal_nonneg
  rw [abs_of_nonneg hn] at hx
  simp only [Pi.pow_apply]
  nlinarith

omit [MetricSpace X] [BorelSpace X] in
lemma exists_compressedDensity {B : ℝ≥0} (hμ : μ ≤ (B : ℝ≥0∞) • m) :
    ∃ u : Lp ℝ 2 m, (∀ᵐ x ∂m, 0 ≤ u x) ∧ (∀ᵐ x ∂m, |u x| ≤ B) ∧
      Integrable u m ∧ (∫ x, u x ∂m) = μ.real univ ∧
      densityMeasure m u = μ ∧ ‖u‖^2 ≤ (B : ℝ)*μ.real univ := by
  let hd := toReal_rnDeriv_memLp hμ
  let u := hd.toLp (fun x => (μ.rnDeriv m x).toReal)
  have he : (u : X → ℝ) =ᵐ[m] (fun x => (μ.rnDeriv m x).toReal) := hd.coeFn_toLp
  have hn : ∀ᵐ x ∂m, 0 ≤ u x := he.mono fun _ hx => hx ▸ ENNReal.toReal_nonneg
  have hb : ∀ᵐ x ∂m, |u x| ≤ B := by
    filter_upwards [he,toReal_rnDeriv_bounded hμ] with x hx hb
    rwa [hx]
  have hi : Integrable u m := Measure.integrable_toReal_rnDeriv.congr he.symm
  have hac : μ ≪ m := Measure.absolutelyContinuous_of_le_smul hμ
  have hmass : (∫ x, u x ∂m) = μ.real univ :=
    (integral_congr_ae he).trans (Measure.integral_toReal_rnDeriv hac)
  refine ⟨u,hn,hb,hi,hmass,?_,?_⟩
  · calc
      densityMeasure m u = m.withDensity (μ.rnDeriv m) := by
        apply withDensity_congr_ae
        filter_upwards [he,Measure.rnDeriv_ne_top μ m] with x hx ht
        rw [hx,ENNReal.ofReal_toReal ht]
      _ = μ := Measure.withDensity_rnDeriv_eq μ m hac
  · have hs : ‖u‖^2 = ∫ x, (u x)^2 ∂m := by
      rw [← real_inner_self_eq_norm_sq,L2.inner_def]
      congr 1; funext x
      simp only [RCLike.inner_apply,conj_trivial,pow_two]
    rw [hs,← hmass,← integral_const_mul]
    apply integral_mono_ae (Lp.memLp u).integrable_sq (hi.const_mul (B : ℝ))
    filter_upwards [hn,hb] with x hn hb
    rw [abs_of_nonneg hn] at hb
    nlinarith

end WeakHessian

end
end

end OAI
end

section
-- module Solutions.OAIQ52_WH.WeakHessian_Transport_PlanHamiltonJacobiAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile223
noncomputable section
namespace WeakHessian
open Set Filter MeasureTheory WeakHessianFunctional WeakHessianTransport
open scoped Topology ENNReal NNReal InnerProductSpace BoundedContinuousFunction

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
variable [CompleteSpace X] [TopologicalSpace.SeparableSpace X] {m : Measure X}

omit [MeasurableSpace X] [BorelSpace X] [CompleteSpace X]
  [TopologicalSpace.SeparableSpace X] in
lemma IsGeodesic.restrictCurve {γ : Curve X} (hγ : IsGeodesic γ) (a b : Time) :
    IsGeodesic (restrictCurve a b γ) := by
  intro s t
  change dist (γ (affineTime a b s)) (γ (affineTime a b t)) =
    |(s : ℝ)-(t : ℝ)| *dist (γ (affineTime a b timeZero)) (γ (affineTime a b timeOne))
  rw [affineTime_zero,affineTime_one,hγ (affineTime a b s) (affineTime a b t),hγ a b]
  have he : (affineTime a b s : ℝ)-(affineTime a b t : ℝ) =
      ((b : ℝ)-(a : ℝ))*((s : ℝ)-(t : ℝ)) := by dsimp [affineTime]; ring
  rw [he,abs_mul,abs_sub_comm (b : ℝ) (a : ℝ)]
  ring

end WeakHessian

end
end InlinedFile223

end OAI
end

section
-- module Solutions.OAIQ52_WH.WeakHessian_Transport_LocalizedActionBound
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section
noncomputable section
namespace WeakHessian
open Set Filter MeasureTheory
open scoped Topology

lemma localizedHeatM_one_le {K a CG T : ℝ} (ha : 0 ≤ a) (hCG : 0 ≤ CG) (hT : 0 ≤ T) :
    1 ≤ localizedHeatM K a CG T := Real.one_le_exp (by positivity)

end WeakHessian

end
end

end OAI
end

section
-- module Solutions.OAIQ52_WH.WeakHessian_LocalBounds_LocalizedScaling
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section
noncomputable section
namespace WeakHessian
open Set Filter
open scoped Topology

lemma localizedActionBound_nonneg {K a c CG T : ℝ} (ha : 0 ≤ a) (hCG : 0 ≤ CG) (hT : 0 ≤ T) :
    0 ≤ localizedActionBound K a c CG T := by
  have hM := localizedHeatM_one_le (K := K) ha hCG hT
  have HR : 0 ≤ 2*|K-a*c| *T*(localizedHeatM K a CG T-1) := by positivity
  unfold localizedActionBound
  nlinarith [sq_nonneg ((K-a*c)*T-1/8)]

lemma localizedActionBound_scaled {K c CG s T : ℝ} (hT : 0 < T) :
    localizedActionBound K (s/T) c CG T =
      1-(K*T-s*c)+2*|K*T-s*c| *(Real.exp (2*(|K| *T+s*CG))-1)+4*(K*T-s*c)^2 := by
  have he : (K-s/T*c)*T = K*T-s*c := by field_simp
  have heM : (|K|+s/T*CG)*T = |K| *T+s*CG := by field_simp
  have ha : |K-s/T*c| *T = |K*T-s*c| := by rw [← he,abs_mul,abs_of_pos hT]
  unfold localizedActionBound localizedHeatM
  rw [show 2*(|K|+s/T*CG)*T = 2*(|K| *T+s*CG) by linarith only [heM]]
  calc
    _ = 1-(K-s/T*c)*T+2*(|K-s/T*c| *T)*(Real.exp (2*(|K| *T+s*CG))-1)+4*((K-s/T*c)*T)^2 := by ring
    _ = _ := by rw [he,ha]

lemma localizedActionBound_scaling_limit (K c CG : ℝ) {s : ℝ} (hs : 0 ≤ s) :
    Tendsto (fun T : ℝ => localizedActionBound K (s/T) c CG T) (𝓝[>] 0) (𝓝 (localActionLimit c CG s)) := by
  have H := (show ContinuousAt (fun T : ℝ =>
      1-(K*T-s*c)+2*|K*T-s*c| *(Real.exp (2*(|K| *T+s*CG))-1)+4*(K*T-s*c)^2) 0 from by fun_prop).tendsto.mono_left (nhdsWithin_le_nhds (s := Ioi (0:ℝ)))
  have He : 1-(K*0-s*c)+2*|K*0-s*c| *(Real.exp (2*(|K| *0+s*CG))-1)+4*(K*0-s*c)^2 = localActionLimit c CG s := by
    simp only [localActionLimit,mul_zero,zero_sub,abs_neg,abs_mul,abs_of_nonneg hs,zero_add,neg_sq]
    ring_nf
  rw [He] at H
  apply H.congr'
  filter_upwards [self_mem_nhdsWithin] with T hT
  exact (localizedActionBound_scaled hT).symm

lemma localized_small_scaled_eventually {K c CG s : ℝ}
    (hs : 8*s*(CG+|c|)*Real.exp (4*CG*s) < 1) :
    ∀ᶠ T : ℝ in 𝓝[>] 0,
      4*(s/T)*(CG+|c|)*(2*T)*localizedHeatM K (s/T) CG (2*T) ≤ 1 := by
  have hc : ContinuousAt (fun T : ℝ => 8*s*(CG+|c|)*Real.exp (4*(|K| *T+s*CG))) 0 := by fun_prop
  have h0 : 8*s*(CG+|c|)*Real.exp (4*(|K| *0+s*CG)) < 1 := by convert hs using 1; congr 1; ring_nf
  filter_upwards [hc.tendsto.eventually (gt_mem_nhds h0) |>.filter_mono nhdsWithin_le_nhds,self_mem_nhdsWithin] with T ht hT
  have hT0 : T ≠ 0 := ne_of_gt hT
  have he : 4*(s/T)*(CG+|c|)*(2*T)*localizedHeatM K (s/T) CG (2*T) =
      8*s*(CG+|c|)*Real.exp (4*(|K| *T+s*CG)) := by
    unfold localizedHeatM
    have harg : 2*(|K|+s/T*CG)*(2*T) = 4*(|K| *T+s*CG) := by field_simp; ring
    rw [harg]; field_simp; ring
  rw [he]; exact ht.le

lemma curvatureTailBound_scaled {K c CG CF s T L C d R S : ℝ} (hT : T ≠ 0) :
    curvatureTailBound K (s/T) c CG (2*T) L (C*Real.exp (2*(s/T)*CF)) d
      (d+(R-S)/(4*T)) R S =
      4*s*(CG+|c|)*L^2*C*Real.exp (4*(|K| *T+s*CG)+2*d^2*T+d*R)*
        Real.exp ((2*s*CF-(R-S)^2/8)/T) := by
  unfold curvatureTailBound localizedHeatM
  have he : 2*(|K|+s/T*CG)*(2*T)+2*(s/T)*CF+
      ((d+(R-S)/(4*T))^2*(2*T)-(d+(R-S)/(4*T))*(R-S)+d*R) =
      4*(|K| *T+s*CG)+2*d^2*T+d*R+(2*s*CF-(R-S)^2/8)/T := by
    field_simp; ring
  have hexp := congrArg Real.exp he
  simp only [Real.exp_add] at hexp
  calc
    _ = (2*(s/T)*(2*T)*(CG+|c|)*L^2*C)*
        (Real.exp (2*(|K|+s/T*CG)*(2*T))*Real.exp (2*(s/T)*CF)*
          Real.exp ((d+(R-S)/(4*T))^2*(2*T)-(d+(R-S)/(4*T))*(R-S)+d*R)) := by ring
    _ = _ := by
      have hp : 2*(s/T)*(2*T) = 4*s := by field_simp; ring
      rw [hp]
      rw [← Real.exp_add,← Real.exp_add,he,Real.exp_add]
      ring

lemma curvatureTailBound_scaling_limit (K c CG CF s L C d R S : ℝ)
    (hgap : 16*s*CF < (R-S)^2) :
    Tendsto (fun T : ℝ => curvatureTailBound K (s/T) c CG (2*T) L
      (C*Real.exp (2*(s/T)*CF)) d (d+(R-S)/(4*T)) R S) (𝓝[>] 0) (𝓝 0) := by
  have hneg : 2*s*CF-(R-S)^2/8 < 0 := by linarith
  have Hexp : Tendsto (fun T : ℝ => Real.exp ((2*s*CF-(R-S)^2/8)/T)) (𝓝[>] 0) (𝓝 0) := by
    have H := Real.tendsto_exp_atBot.comp (tendsto_inv_nhdsGT_zero.const_mul_atTop_of_neg hneg)
    simpa only [Function.comp_def,div_eq_mul_inv] using H
  have Hc := (show ContinuousAt (fun T : ℝ => 4*s*(CG+|c|)*L^2*C*
    Real.exp (4*(|K| *T+s*CG)+2*d^2*T+d*R)) 0 from by fun_prop).tendsto.mono_left (nhdsWithin_le_nhds (s := Ioi (0:ℝ)))
  have H := Hc.mul Hexp
  simp only [mul_zero] at H
  apply H.congr'
  filter_upwards [self_mem_nhdsWithin] with T hT
  exact (curvatureTailBound_scaled (ne_of_gt hT)).symm

lemma localActionLimit_slope_limit (c CG : ℝ) :
    Tendsto (fun s : ℝ => (localActionLimit c CG s-1)/s) (𝓝[>] 0) (𝓝 c) := by
  have H := (show ContinuousAt (fun s : ℝ => c+2*|c| *(Real.exp (2*CG*s)-1)+4*c^2*s) 0
    from by fun_prop).tendsto.mono_left (nhdsWithin_le_nhds (s := Ioi (0:ℝ)))
  simp only [mul_zero,Real.exp_zero,sub_self,add_zero] at H
  apply H.congr'
  filter_upwards [self_mem_nhdsWithin] with s hs
  have hs0 : s ≠ 0 := ne_of_gt hs
  unfold localActionLimit
  field_simp
  ring

lemma eventually_local_scaling_admissible (c CG CF : ℝ) {g : ℝ} (hg : 0 < g) :
    ∀ᶠ s : ℝ in 𝓝[>] 0,
      8*s*(CG+|c|)*Real.exp (4*CG*s) < 1 ∧ 16*s*CF < g^2 := by
  have h1 : ContinuousAt (fun s : ℝ => 8*s*(CG+|c|)*Real.exp (4*CG*s)) 0 := by fun_prop
  have h2 : ContinuousAt (fun s : ℝ => 16*s*CF) 0 := by fun_prop
  have H1 := h1.eventually_lt continuousAt_const (by simp : 8*(0:ℝ)*(CG+|c|)*Real.exp (4*CG*0) < 1)
  have H2 := h2.eventually_lt continuousAt_const (by simpa using sq_pos_of_pos hg : 16*(0:ℝ)*CF < g^2)
  exact (H1.and H2).filter_mono nhdsWithin_le_nhds
end WeakHessian

end
end

end OAI
end

section
-- module Solutions.OAIQ52_WH.WeakHessian_Geodesics_LocalTwoLegLimit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section
noncomputable section
namespace WeakHessian
open Set Filter
open scoped Topology

lemma vanishing_diffusion_local_two_leg {Z E A B C d s f L R a₀ : ℝ}
    {act err₀ err₁ : ℝ → ℝ} (hs : 0 ≤ s) (hd : 0 ≤ d) (hL : 0 ≤ L)
    (hact : Tendsto act (𝓝[>] 0) (𝓝 a₀))
    (herr₀ : Tendsto err₀ (𝓝[>] 0) (𝓝 0)) (herr₁ : Tendsto err₁ (𝓝[>] 0) (𝓝 0))
    (h : ∀ᶠ T : ℝ in 𝓝[>] 0,∃ M : ℝ,0 ≤ M ∧ M^2 ≤ A+B*T+16*T^2*d^2 ∧
      Z ≤ E*act T+err₀ T+err₁ T+T*(C+2*d*M)+s*(f+L*(2*M+R))) :
    Z ≤ E*a₀+s*(f+L*(2*Real.sqrt A+R)) := by
  have H : ∀ᶠ T : ℝ in 𝓝[>] 0,
      Z ≤ E*act T+err₀ T+err₁ T+T*(C+2*d*Real.sqrt (A+B*T+16*T^2*d^2))+
        s*(f+L*(2*Real.sqrt (A+B*T+16*T^2*d^2)+R)) := by
    filter_upwards [h,self_mem_nhdsWithin] with T hT hTp
    obtain ⟨M,hMn,hM,hZ⟩ := hT
    have hMs := Real.le_sqrt_of_sq_le hM
    apply hZ.trans
    have ht : 0 ≤ T := le_of_lt hTp
    gcongr
  have hmom := (show ContinuousAt (fun T : ℝ =>
      T*(C+2*d*Real.sqrt (A+B*T+16*T^2*d^2))+s*(f+L*(2*Real.sqrt (A+B*T+16*T^2*d^2)+R))) 0
    from by fun_prop).tendsto.mono_left (nhdsWithin_le_nhds (s := Ioi (0:ℝ)))
  have hlim := ((((tendsto_const_nhds (x := E)).mul hact).add herr₀).add herr₁).add hmom
  have H' : ∀ᶠ T : ℝ in 𝓝[>] 0,
      Z ≤ E*act T+err₀ T+err₁ T+
        (T*(C+2*d*Real.sqrt (A+B*T+16*T^2*d^2))+s*(f+L*(2*Real.sqrt (A+B*T+16*T^2*d^2)+R))) := by
    filter_upwards [H] with T hT
    simpa only [add_assoc] using hT
  have HH := ge_of_tendsto hlim H'
  simpa only [mul_zero,zero_pow (by norm_num : (2:ℕ) ≠ 0),zero_mul,add_zero,zero_add] using HH

lemma midpoint_bound_of_local_two_leg_approx {D c CG CF L f₀ f₁ fz LD J : ℝ}
    (h : ∀ᶠ s : ℝ in 𝓝[>] 0,∀ᶠ r : ℝ in 𝓝[>] 0,∀ δ q : ℝ,0 < δ → 0 < q →
      D^2/4-LD*(r+δ*(D/2+2*r))-J*q ≤
        (D/2+2*r)^2*localActionLimit c CG s+
        s*(2*fz-f₀-f₁+L*(2*Real.sqrt (4*r^2+16*s*CF)+2*r+δ*(D+4*r)))) :
    (f₀+f₁)/2-c/8*D^2 ≤ fz := by
  have Hs : ∀ᶠ s : ℝ in 𝓝[>] 0,
      D^2/4 ≤ (D/2)^2*localActionLimit c CG s+
        s*(2*fz-f₀-f₁+L*(2*Real.sqrt (16*s*CF))) := by
    filter_upwards [h] with s hs
    have Hr : ∀ᶠ r : ℝ in 𝓝[>] 0,
        D^2/4-LD*r ≤ (D/2+2*r)^2*localActionLimit c CG s+
          s*(2*fz-f₀-f₁+L*(2*Real.sqrt (4*r^2+16*s*CF)+2*r)) := by
      filter_upwards [hs] with r hr
      have Hδ (δ : ℝ) (hδ : 0 < δ) :
          D^2/4-LD*(r+δ*(D/2+2*r)) ≤ (D/2+2*r)^2*localActionLimit c CG s+
            s*(2*fz-f₀-f₁+L*(2*Real.sqrt (4*r^2+16*s*CF)+2*r+δ*(D+4*r))) := by
        have H := le_at_zero_of_positive
          (f := fun q => D^2/4-LD*(r+δ*(D/2+2*r))-J*q)
          (g := fun _ => (D/2+2*r)^2*localActionLimit c CG s+
            s*(2*fz-f₀-f₁+L*(2*Real.sqrt (4*r^2+16*s*CF)+2*r+δ*(D+4*r))))
          (by fun_prop) continuousAt_const (fun q hq => hr δ q hδ hq)
        simpa only [mul_zero,sub_zero] using H
      have H := le_at_zero_of_positive
        (f := fun δ => D^2/4-LD*(r+δ*(D/2+2*r)))
        (g := fun δ => (D/2+2*r)^2*localActionLimit c CG s+
          s*(2*fz-f₀-f₁+L*(2*Real.sqrt (4*r^2+16*s*CF)+2*r+δ*(D+4*r))))
        (by fun_prop) (by fun_prop) Hδ
      simpa only [zero_mul,add_zero] using H
    have H := le_of_tendsto_of_tendsto
      ((show ContinuousAt (fun r : ℝ => D^2/4-LD*r) 0 from by fun_prop).tendsto.mono_left nhdsWithin_le_nhds)
      ((show ContinuousAt (fun r : ℝ => (D/2+2*r)^2*localActionLimit c CG s+
        s*(2*fz-f₀-f₁+L*(2*Real.sqrt (4*r^2+16*s*CF)+2*r))) 0 from by fun_prop).tendsto.mono_left nhdsWithin_le_nhds) Hr
    simpa only [mul_zero,zero_pow (by norm_num : (2:ℕ) ≠ 0),zero_mul,zero_add,add_zero,sub_zero] using H
  have Hq : ∀ᶠ s : ℝ in 𝓝[>] 0,
      0 ≤ D^2/4*((localActionLimit c CG s-1)/s)+(2*fz-f₀-f₁)+2*L*Real.sqrt (16*s*CF) := by
    filter_upwards [Hs,self_mem_nhdsWithin] with s hs hsp
    have hpos : 0 < s := hsp
    apply (mul_nonneg_iff_of_pos_left hpos).mp
    field_simp [hpos.ne']
    ring_nf at hs ⊢
    nlinarith only [hs]
  have hlim := localActionLimit_slope_limit c CG
  have hsqrt : Tendsto (fun s : ℝ => Real.sqrt (16*s*CF)) (𝓝[>] (0:ℝ)) (𝓝 0) := by
    convert (show ContinuousAt (fun s : ℝ => Real.sqrt (16*s*CF)) 0 from by fun_prop).tendsto.mono_left nhdsWithin_le_nhds using 1
    all_goals try with_reducible_and_instances rfl
    simp
  have HH := ge_of_tendsto
    ((((tendsto_const_nhds (x := D^2/4)).mul hlim).add
      (tendsto_const_nhds (x := 2*fz-f₀-f₁))).add ((tendsto_const_nhds (x := 2*L)).mul hsqrt)) Hq
  nlinarith [HH]
end WeakHessian

end
end

end OAI
end

section
-- module Solutions.OAIQ52_WH.WeakHessian_Entropy_EntropyDensityBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section
noncomputable section
namespace WeakHessian
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal

variable {X : Type*} [MeasurableSpace X] {m μ : Measure X}
variable [SigmaFinite m] [IsProbabilityMeasure μ]

lemma entropyReal_le_log_density_cap (hμ : FiniteEntropy m μ)
    {B : ℝ≥0} (hB : 0 < B) (hd : μ ≤ (B : ℝ≥0∞) • m) :
    entropyReal m μ ≤ Real.log B := by
  have hr := hμ.1.ae_le (rnDeriv_le_of_le_smul hd)
  have hp := Measure.rnDeriv_pos hμ.1
  have ht := hμ.1.ae_le (Measure.rnDeriv_lt_top μ m)
  have hlog : ∀ᵐ x ∂μ,llr μ m x ≤ Real.log B := by
    filter_upwards [hr,hp,ht] with x hx hp ht
    change Real.log (μ.rnDeriv m x).toReal ≤ Real.log B
    apply (Real.log_le_log_iff (ENNReal.toReal_pos hp.ne' ht.ne)
      (show 0 < (B : ℝ) from hB)).mpr
    exact (ENNReal.toReal_mono ENNReal.coe_ne_top hx).trans_eq (ENNReal.coe_toReal B)
  simpa only [entropyReal,integral_const,probReal_univ,one_smul] using
    integral_mono_ae hμ.2 (integrable_const (Real.log (B : ℝ))) hlog

lemma entropyReal_lower_confinement (hμ : FiniteEntropy m μ) {V : X → ℝ}
    (hV : Integrable V μ) (he : Integrable (fun x => Real.exp (-V x)) m) :
    1-(∫ x,V x ∂μ)-(∫ x,Real.exp (-V x) ∂m) ≤ entropyReal m μ := by
  have hρ := Measure.integrable_toReal_rnDeriv (μ := μ) (ν := m)
  have hp := (integrable_toReal_rnDeriv_mul_iff hμ.1).mpr hV
  have hl := (integrable_rnDeriv_mul_log_iff hμ.1).mpr hμ.2
  have H := integral_mono_ae ((hp.neg.sub he).add hρ) hl (ae_of_all _ fun x => by
    have H := mul_log_fenchel (r := (μ.rnDeriv m x).toReal) (a := -V x) ENNReal.toReal_nonneg
    simpa only [mul_neg,Pi.add_apply,Pi.sub_apply,Pi.neg_apply] using H)
  simp only [Pi.add_apply,Pi.sub_apply,Pi.neg_apply] at H
  have hiA := integral_add (hp.neg.sub he) hρ
  have hiS := integral_sub hp.neg he
  simp only [Pi.sub_apply,Pi.neg_apply] at hiA hiS
  rw [hiA,hiS,integral_neg,
    integral_toReal_rnDeriv_mul hμ.1,Measure.integral_toReal_rnDeriv hμ.1,
    ← entropyReal_eq_integral_density hμ.1] at H
  simp only [probReal_univ] at H
  linarith

lemma entropyReal_exponential_upper (hμ : FiniteEntropy m μ)
    {V : X → ℝ} (hV : Measurable V) {C : ℝ} (hC : ∀ x,|V x| ≤ C)
    {B : ℝ≥0} (hB : 0 < B) (hd : μ ≤ (B : ℝ≥0∞) • m) :
    entropyReal (exponentialMeasure m V) μ ≤ Real.log B - ∫ x,V x ∂μ := by
  have hi : Integrable V μ := Integrable.of_bound hV.aestronglyMeasurable C
    (ae_of_all _ fun x => by simpa only [Real.norm_eq_abs] using hC x)
  rw [entropyReal_exponentialMeasure hμ hV hi]
  exact sub_le_sub_right (entropyReal_le_log_density_cap hμ hB hd) _

end WeakHessian

end
end

end OAI
end

section
-- module Solutions.OAIQ52_WH.WeakHessian_Geodesics_TwoLegEstimate
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section
noncomputable section
namespace WeakHessian
open Set Filter MeasureTheory WeakHessianTransport WeakHessianFunctional
open scoped Topology ENNReal NNReal

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]

lemma integral_lipschitz_deviation {μ : Measure X} [IsProbabilityMeasure μ]
    {F : X → ℝ} {L : ℝ≥0} (hF : LipschitzWith L F) (o : X)
    (hi : Integrable (fun x => dist x o) μ) :
    |(∫ x,F x ∂μ)-F o| ≤ (L:ℝ)*(∫ x,dist x o ∂μ) := by
  have hbound (x : X) : |F x-F o| ≤ (L:ℝ)*dist x o := by
    simpa only [Real.dist_eq] using hF.dist_le_mul x o
  have hd : Integrable (fun x => F x-F o) μ :=
    (hi.const_mul (L:ℝ)).mono' (hF.continuous.sub continuous_const).aestronglyMeasurable
      (ae_of_all _ fun x => by simpa only [Real.norm_eq_abs] using hbound x)
  have hFi : Integrable F μ := by
    have H := hd.add (integrable_const (F o))
    change Integrable (fun x => F x-F o+F o) μ at H
    simpa only [sub_add_cancel] using H
  have H := abs_integral_le_integral_abs (f := fun x => F x-F o) (μ := μ)
  rw [integral_sub hFi (integrable_const (F o)),integral_const,probReal_univ,one_smul] at H
  exact H.trans (by
    rw [← integral_const_mul]
    exact integral_mono_ae hd.abs (hi.const_mul (L:ℝ)) (ae_of_all _ hbound))

lemma integral_dist_le_of_ae_ball {μ : Measure X} [IsProbabilityMeasure μ]
    (o : X) {r : ℝ} (hs : ∀ᵐ x ∂μ,dist x o ≤ r) :
    Integrable (fun x => dist x o) μ ∧ (∫ x,dist x o ∂μ) ≤ r := by
  have hi : Integrable (fun x => dist x o) μ := Integrable.of_bound (by fun_prop) r
    (hs.mono fun x hx => by simpa only [Real.norm_of_nonneg dist_nonneg] using hx)
  exact ⟨hi,by simpa only [integral_const,probReal_univ,one_smul] using
    integral_mono_ae hi (integrable_const r) hs⟩

end WeakHessian

end
end

end OAI
end

section
-- module Solutions.OAIQ52_WH.WeakHessian_Entropy_EntropyDrop
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section
noncomputable section
namespace WeakHessian
open Set Filter MeasureTheory WeakHessianTransport WeakHessianFunctional
open scoped Topology ENNReal NNReal

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
variable {m : Measure X} [SigmaFinite m]
lemma entropy_exponential_drop_bound {F : X → ℝ} {L : ℝ≥0}
    (hF : LipschitzWith L F) {CF : ℝ} (hFb : ∀ x,|F x| ≤ CF)
    {a c : ℝ} (ha : 0 ≤ a) (hc : 0 ≤ c)
    (o x₁ : X) (μ ν : ProbabilityMeasure X)
    (hμE : FiniteEntropy m (μ:Measure X)) (hνE : FiniteEntropy m (ν:Measure X))
    (hνi : Integrable (fun x => dist x o) (ν:Measure X))
    (he : Integrable (fun x => Real.exp (-(c*dist x o))) m)
    {B : ℝ≥0} (hB : 0 < B) (hμB : (μ:Measure X) ≤ (B:ℝ≥0∞) • m)
    {r : ℝ} (hs : ∀ᵐ x ∂(μ:Measure X),dist x x₁ ≤ r) :
    entropyReal (exponentialMeasure m (fun x => a*F x)) (μ:Measure X)-
      entropyReal (exponentialMeasure m (fun x => a*F x)) (ν:Measure X) ≤
      |Real.log (B:ℝ)|+(∫ x,Real.exp (-(c*dist x o)) ∂m)+1+
        c*(∫ x,dist x o ∂(ν:Measure X))+
        a*(F o-F x₁+(L:ℝ)*((∫ x,dist x o ∂(ν:Measure X))+r)) := by
  have hVm : Measurable (fun x => a*F x) := (continuous_const.mul hF.continuous).measurable
  have hVb : ∀ x, |a*F x| ≤ |a| *CF := fun x => by
    rw [abs_mul]; exact mul_le_mul_of_nonneg_left (hFb x) (abs_nonneg a)
  have hVi : Integrable (fun x => a*F x) (ν:Measure X) := Integrable.of_bound hVm.aestronglyMeasurable (|a| *CF)
    (ae_of_all _ fun x => by simpa only [Real.norm_eq_abs] using hVb x)
  have hupper := entropyReal_exponential_upper hμE hVm hVb hB hμB
  have hlower := entropyReal_lower_confinement (V := fun x => c*dist x o) hνE
    (by simpa only [abs_of_nonneg hc] using hνi.const_mul |c|) he
  have hchange := entropyReal_exponentialMeasure hνE hVm hVi
  rw [integral_const_mul] at hupper hlower hchange
  have hFν := (abs_le.mp (integral_lipschitz_deviation hF o hνi)).2
  obtain ⟨hμi,hμr⟩ := integral_dist_le_of_ae_ball x₁ hs
  have hFμ := (abs_le.mp (integral_lipschitz_deviation hF x₁ hμi)).1
  have hFμ' := mul_le_mul_of_nonneg_left hμr L.property
  have hdrop : entropyReal (exponentialMeasure m (fun x => a*F x)) (μ:Measure X)-
      entropyReal (exponentialMeasure m (fun x => a*F x)) (ν:Measure X) ≤
      |Real.log (B:ℝ)|+(∫ x,Real.exp (-(c*dist x o)) ∂m)+1+c*(∫ x,dist x o ∂(ν:Measure X))+
        a*(F o-F x₁+(L:ℝ)*((∫ x,dist x o ∂(ν:Measure X))+r)) := by
    have H := le_abs_self (Real.log (B:ℝ))
    have Hf : (∫ x,F x ∂(ν:Measure X))-(∫ x,F x ∂(μ:Measure X)) ≤
        F o-F x₁+(L:ℝ)*((∫ x,dist x o ∂(ν:Measure X))+r) := by
      change (∫ x,F x ∂(ν:Measure X))-F o ≤ (L:ℝ)*(∫ x,dist x o ∂(ν:Measure X)) at hFν
      change -((L:ℝ)*(∫ x,dist x x₁ ∂(μ:Measure X))) ≤ (∫ x,F x ∂(μ:Measure X))-F x₁ at hFμ
      change (L:ℝ)*(∫ x,dist x x₁ ∂(μ:Measure X)) ≤ (L:ℝ)*r at hFμ'
      nlinarith only [hFν,hFμ,hFμ']
    have Ha := mul_le_mul_of_nonneg_left Hf ha
    linarith
  exact hdrop

end WeakHessian

end
end

end OAI
end

section
-- module Solutions.OAIQ52_WH.WeakHessian_Geodesics_MidpointDualTests
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section
noncomputable section
namespace WeakHessian
open Set Filter MeasureTheory WeakHessianTransport
open scoped Topology ENNReal NNReal BoundedContinuousFunction

variable {X : Type*} [MetricSpace X]

lemma midpointDualTest_nonneg (o : X) (R : ℝ) (x : X) : 0 ≤ midpointDualTest o R x := by
  simp only [midpointDualTest_apply]; positivity

lemma midpointDualTest_compact [ProperSpace X] (o : X) {R : ℝ} (hR : 0 ≤ R) :
    HasCompactSupport (midpointDualTest o R : X → ℝ) := by
  apply HasCompactSupport.intro' (isCompact_closedBall o R) Metric.isClosed_closedBall
  intro x hx
  have hdist : R ≤ dist x o := le_of_lt (lt_of_not_ge hx)
  simp only [midpointDualTest_apply]
  rw [max_eq_right (by nlinarith [dist_nonneg (x := x) (y := o)] : R^2-dist x o^2 ≤ 0),zero_div]

lemma midpointDualTest_hopf_one [ProperSpace X] (o : X) (R : ℝ) :
    boundedHopfMap (midpointDualTest o R) 1 o = R^2/2 := by
  rw [boundedHopfMap_apply_pos _ zero_lt_one]
  apply le_antisymm
  · have H := hopfLax_le_self (midpointDualTest_nonneg o R) zero_lt_one o
    simpa only [midpointDualTest_apply,dist_self,zero_pow (by norm_num : (2:ℕ) ≠ 0),sub_zero,max_eq_left (sq_nonneg R)] using H
  · apply le_csInf ⟨hopfObjective (midpointDualTest o R) 1 o o,mem_range_self o⟩
    rintro v ⟨x,rfl⟩
    dsimp only [hopfObjective]
    rw [midpointDualTest_apply,dist_comm o x]
    have H := le_max_left (R^2-dist x o^2) 0
    nlinarith only [H]

lemma midpointDualTest_sum_le (x₀ x₁ z : X) {R : ℝ} (hR : dist x₀ x₁ ≤ R) :
    midpointDualTest x₀ R z+midpointDualTest x₁ R z ≤ R^2-dist x₀ x₁^2/4 := by
  have hRn : 0 ≤ R := dist_nonneg.trans hR
  have hDsq : dist x₀ x₁^2 ≤ R^2 := (sq_le_sq₀ dist_nonneg hRn).mpr hR
  have htri : dist x₀ x₁ ≤ dist z x₀+dist z x₁ := by
    simpa only [dist_comm x₀ z] using dist_triangle x₀ z x₁
  have hsq : dist x₀ x₁^2 ≤ 2*(dist z x₀^2+dist z x₁^2) := by
    nlinarith [sq_nonneg (dist z x₀-dist z x₁),dist_nonneg (x := z) (y := x₀),dist_nonneg (x := z) (y := x₁),dist_nonneg (x := x₀) (y := x₁)]
  simp only [midpointDualTest_apply]
  rcases le_total (R^2-dist z x₀^2) 0 with h₀ | h₀
  · rw [max_eq_right h₀]
    have H := max_le (by nlinarith [sq_nonneg (dist z x₁)] : R^2-dist z x₁^2 ≤ R^2) (sq_nonneg R)
    nlinarith
  · rw [max_eq_left h₀]
    rcases le_total (R^2-dist z x₁^2) 0 with h₁ | h₁
    · rw [max_eq_right h₁]
      nlinarith [sq_nonneg (dist z x₀)]
    · rw [max_eq_left h₁]
      nlinarith only [hsq]

section Laws
variable [ProperSpace X] [MeasurableSpace X] [BorelSpace X]

lemma hopf_integral_terminal_lower (f : X →ᵇ ℝ) {D : ℝ≥0}
    (hD : LipschitzWith D (boundedHopfMap f 1)) (μ : ProbabilityMeasure X)
    (o : X) {r q : ℝ} (hs : ∀ᵐ x ∂(μ:Measure X),dist x o ≤ r) (hq : 0 < q) :
    boundedHopfMap f 1 o-(D:ℝ)*r-2*‖f‖*q ≤ ∫ x,boundedHopfMap f (q+1) x ∂(μ:Measure X) := by
  have htime := (boundedHopfMap_time_lipschitz f zero_lt_one).dist_le_mul (q+1) (by change (1:ℝ) ≤ q+1; linarith)
    1 (by simp : (1:ℝ) ∈ Ici 1)
  have htime' : dist (boundedHopfMap f (q+1)) (boundedHopfMap f 1) ≤ 2*‖f‖*q := by
    change dist (boundedHopfMap f (q+1)) (boundedHopfMap f 1) ≤ (2*‖f‖/1)*dist (q+1) 1 at htime
    simpa only [div_one,Real.dist_eq,add_sub_cancel_right,abs_of_pos hq] using htime
  have hlower : ∀ᵐ x ∂(μ:Measure X),boundedHopfMap f 1 o-(D:ℝ)*r-2*‖f‖*q ≤ boundedHopfMap f (q+1) x := by
    filter_upwards [hs] with x hx
    have HD := hD.dist_le_mul x o
    have HT := (BoundedContinuousFunction.dist_coe_le_dist (f := boundedHopfMap f (q+1)) (g := boundedHopfMap f 1) x).trans htime'
    have HB := mul_le_mul_of_nonneg_left hx D.property
    rw [Real.dist_eq] at HD HT
    have HDlo := (abs_le.mp HD).1
    have HTlo := (abs_le.mp HT).1
    change -(↑D*dist x o) ≤ boundedHopfMap f 1 x-boundedHopfMap f 1 o at HDlo
    change -(2*‖f‖*q) ≤ boundedHopfMap f (q+1) x-boundedHopfMap f 1 x at HTlo
    calc
      _ ≤ boundedHopfMap f 1 o-(D:ℝ)*dist x o-2*‖f‖*q :=
        sub_le_sub_right (sub_le_sub_left HB _) _
      _ ≤ boundedHopfMap f 1 x-2*‖f‖*q := sub_le_sub_right (by linarith only [HDlo]) _
      _ ≤ boundedHopfMap f (q+1) x := by linarith only [HTlo]
  have H := integral_mono_ae (integrable_const _) ((boundedHopfMap f (q+1)).integrable (μ := (μ:Measure X))) hlower
  simpa only [Pi.add_apply,integral_const,probReal_univ,one_smul] using H

lemma midpoint_dual_lower (x₀ x₁ : X) {R : ℝ} (hR : dist x₀ x₁ ≤ R)
    (μ₀ μ₁ ν : ProbabilityMeasure X) {D₀ D₁ : ℝ≥0}
    (hD₀ : LipschitzWith D₀ (boundedHopfMap (midpointDualTest x₀ R) 1))
    (hD₁ : LipschitzWith D₁ (boundedHopfMap (midpointDualTest x₁ R) 1))
    {r₀ r₁ q : ℝ} (hs₀ : ∀ᵐ x ∂(μ₀:Measure X),dist x x₀ ≤ r₀)
    (hs₁ : ∀ᵐ x ∂(μ₁:Measure X),dist x x₁ ≤ r₁) (hq : 0 < q) :
    dist x₀ x₁^2/4-(D₀:ℝ)*r₀-(D₁:ℝ)*r₁-
      2*(‖midpointDualTest x₀ R‖+‖midpointDualTest x₁ R‖)*q ≤
      ((∫ x,boundedHopfMap (midpointDualTest x₀ R) (q+1) x ∂(μ₀:Measure X))-
        (∫ x,boundedHopfMap (midpointDualTest x₀ R) q x ∂(ν:Measure X)))+
      ((∫ x,boundedHopfMap (midpointDualTest x₁ R) (q+1) x ∂(μ₁:Measure X))-
        (∫ x,boundedHopfMap (midpointDualTest x₁ R) q x ∂(ν:Measure X))) := by
  have H₀ := hopf_integral_terminal_lower _ hD₀ μ₀ x₀ hs₀ hq
  have H₁ := hopf_integral_terminal_lower _ hD₁ μ₁ x₁ hs₁ hq
  rw [midpointDualTest_hopf_one] at H₀ H₁
  have Hinit : (∫ x,boundedHopfMap (midpointDualTest x₀ R) q x ∂(ν:Measure X))+
      (∫ x,boundedHopfMap (midpointDualTest x₁ R) q x ∂(ν:Measure X)) ≤ R^2-dist x₀ x₁^2/4 := by
    rw [← integral_add (BoundedContinuousFunction.integrable (ν:Measure X) _) (BoundedContinuousFunction.integrable (ν:Measure X) _)]
    have hpoint (z : X) : boundedHopfMap (midpointDualTest x₀ R) q z+
        boundedHopfMap (midpointDualTest x₁ R) q z ≤ R^2-dist x₀ x₁^2/4 := by
      rw [boundedHopfMap_apply_pos _ hq,boundedHopfMap_apply_pos _ hq]
      exact (add_le_add (hopfLax_le_self (midpointDualTest_nonneg x₀ R) hq z)
        (hopfLax_le_self (midpointDualTest_nonneg x₁ R) hq z)).trans (midpointDualTest_sum_le x₀ x₁ z hR)
    have H := integral_mono_ae (Integrable.add
      ((boundedHopfMap (midpointDualTest x₀ R) q).integrable (μ := (ν:Measure X)))
      ((boundedHopfMap (midpointDualTest x₁ R) q).integrable (μ := (ν:Measure X))))
      (integrable_const (R^2-dist x₀ x₁^2/4)) (ae_of_all (ν:Measure X) hpoint)
    simpa only [Pi.add_apply,integral_const,probReal_univ,one_smul] using H
  linarith only [H₀,H₁,Hinit]
end Laws
end WeakHessian

end
end

end OAI
end

section
-- module Solutions.OAIQ52_WH.WeakHessian_LocalBounds_WeightedInitialLaw
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section
noncomputable section
namespace WeakHessian
open Set Filter MeasureTheory WeakHessianTransport
open scoped Topology ENNReal NNReal

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
variable [TopologicalSpace.SeparableSpace X] {m : Measure X} [SigmaFinite m]
omit [BorelSpace X] [TopologicalSpace.SeparableSpace X] [SigmaFinite m] in
lemma exists_weighted_initial_density (hfin : FiniteOnBoundedSets m) (o : X)
    {V : X → ℝ} {CV : ℝ} (hVb : ∀ x,|V x| ≤ CV)
    (μ : ProbabilityMeasure X) {B : ℝ≥0} (hcap : (μ:Measure X) ≤ (B:ℝ≥0∞) • m) :
    ∃ C : ℝ≥0,∃ u : Lp ℝ 2 (exponentialMeasure m V),
      (∀ᵐ x ∂exponentialMeasure m V,0 ≤ u x) ∧
      (∀ᵐ x ∂exponentialMeasure m V,|u x| ≤ C) ∧
      (∫ x,u x ∂exponentialMeasure m V) = 1 ∧
      densityMeasure (exponentialMeasure m V) u = (μ:Measure X) := by
  let ν := exponentialMeasure m V
  obtain ⟨hmν,hνm⟩ := exponentialMeasure_comparable (m := m) hVb
  have hnfin := hfin.of_le_smul (C := (Real.exp CV).toNNReal) hνm
  let : SigmaFinite ν := sigmaFinite_of_finiteOnBoundedSets ν hnfin o
  let C : ℝ≥0 := B*(Real.exp CV).toNNReal
  have hcapν : (μ:Measure X) ≤ (C:ℝ≥0∞) • ν := hcap.trans (by
    calc
      (B:ℝ≥0∞) • m ≤ (B:ℝ≥0∞) • (((Real.exp CV).toNNReal:ℝ≥0∞) • ν) := by
        gcongr
        exact hmν
      _ = (C:ℝ≥0∞) • ν := by rw [smul_smul]; rfl)
  obtain ⟨u,hun,hub,hui,hum,hul,_⟩ := exists_compressedDensity hcapν
  exact ⟨C,u,hun,hub,by simpa only [probReal_univ] using hum,hul⟩
end WeakHessian

end
end

end OAI
end

section
-- module Solutions.OAIQ52_WH.WeakHessian_HeatFlow_CommonLocalHeatLegs
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section
noncomputable section
namespace WeakHessian
open Set Filter MeasureTheory WeakHessianTransport WeakHessianFunctional
open scoped Topology ENNReal NNReal BoundedContinuousFunction

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
variable [CompleteSpace X] [ProperSpace X] [TopologicalSpace.SeparableSpace X]
variable {m : Measure X} [SigmaFinite m]

lemma WeakHessianUpperBound.rcd_common_local_heat_legs {K N : ℝ}
    (hN : 1 < N) (hrcd : RCD m K N) (hfull : FullSupport m) (hfin : FiniteOnBoundedSets m)
    {F G : X → ℝ} (hHess : WeakHessianUpperBound m F G)
    {L : ℝ≥0} (hF : LipschitzWith L F) {CF CG : ℝ} (hFb : ∀ x,|F x| ≤ CF)
    (hGb : ∀ x,|G x| ≤ CG) (hGc : Continuous G)
    (o x₀ x₁ : X) (μ₀ : ProbabilityMeasure X) {r : ℝ} (hr : 0 ≤ r)
    (hsμ : ∀ᵐ x ∂(μ₀:Measure X),dist x o ≤ r)
    {B : ℝ≥0} (hB : 0 < B) (hcap : (μ₀:Measure X) ≤ (B:ℝ≥0∞) • m)
    {d : ℝ} (hd : 0 < d) (he : Integrable (fun x => Real.exp (-(d*dist x o))) m)
    (hdecay : MemLp (fun x => Real.exp (-d*dist x o)) 2 m)
    {π₀ π₁ : Measure (Curve X)} {C₀ C₁ : ℝ≥0} (hC₀ : 0 < C₀) (hC₁ : 0 < C₁)
    (hπ₀ : IsTestPlan m π₀) (hπ₁ : IsTestPlan m π₁)
    (hb₀ : BoundedTracks π₀) (hb₁ : BoundedTracks π₁)
    (hg₀ : ∀ᵐ γ ∂π₀,IsGeodesic γ) (hg₁ : ∀ᵐ γ ∂π₁,IsGeodesic γ)
    (hi₀ : π₀.map (fun γ => γ timeZero) = (μ₀:Measure X))
    (hi₁ : π₁.map (fun γ => γ timeZero) = (μ₀:Measure X))
    (hcap₀ : ∀ t : Time,π₀.map (fun γ => γ t) ≤ (C₀:ℝ≥0∞) • m)
    (hcap₁ : ∀ t : Time,π₁.map (fun γ => γ t) ≤ (C₁:ℝ≥0∞) • m)
    {D₀ D₁ S R c : ℝ} (hD₀ : 0 ≤ D₀) (hD₁ : 0 ≤ D₁)
    (hs₀ : ∀ᵐ γ ∂π₀,dist (γ timeOne) x₀ ≤ r)
    (hs₁ : ∀ᵐ γ ∂π₁,dist (γ timeOne) x₁ ≤ r)
    (hl₀ : ∀ᵐ γ ∂π₀,dist (γ timeZero) (γ timeOne) ≤ D₀)
    (hl₁ : ∀ᵐ γ ∂π₁,dist (γ timeZero) (γ timeOne) ≤ D₁)
    (hE₀ : planKineticCost π₀ ≤ D₀^2) (hE₁ : planKineticCost π₁ ≤ D₁^2)
    (htracks₀ : ∀ᵐ γ ∂π₀,∀ t : Time,dist (γ t) o < S)
    (htracks₁ : ∀ᵐ γ ∂π₁,∀ t : Time,dist (γ t) o < S)
    (hlocal : ∀ x,dist x o < R → G x ≤ c)
    {Rd : ℝ} (hRd : dist x₀ x₁ ≤ Rd) {LD₀ LD₁ : ℝ≥0}
    (hLD₀ : LipschitzWith LD₀ (boundedHopfMap (midpointDualTest x₀ Rd) 1))
    (hLD₁ : LipschitzWith LD₁ (boundedHopfMap (midpointDualTest x₁ Rd) 1))
    {a T U δ β q : ℝ} (ha : 0 < a) (hT : 0 ≤ T) (hTU : T < U)
    (hδ : 0 < δ) (hq : 0 < q) (hdβ : d ≤ β)
    (hsmall : 4*a*(CG+|c|)*U*localizedHeatM K a CG U ≤ 1) :
    ∃ M : ℝ,0 ≤ M ∧
      M^2 ≤ 4*r^2+8*T*(|Real.log (B:ℝ)|+(∫ x,Real.exp (-(d*dist x o)) ∂m)+1)+
        16*(T*a)*CF+16*T^2*d^2 ∧
      dist x₀ x₁^2/4-(LD₀:ℝ)*(r+δ*D₀)-(LD₁:ℝ)*(r+δ*D₁)-
        2*(‖midpointDualTest x₀ Rd‖+‖midpointDualTest x₁ Rd‖)*q ≤
        (D₀^2+D₁^2)/2*localizedActionBound K a c CG T+
        curvatureTailBound K a c CG U (hopfUniformLip (midpointDualTest x₀ Rd) q)
          (((C₀:ℝ)+1)*(‖hdecay.toLp (fun x => Real.exp (-d*dist x o))‖+1)*Real.exp (2*a*CF)) d β R S+
        curvatureTailBound K a c CG U (hopfUniformLip (midpointDualTest x₁ Rd) q)
          (((C₁:ℝ)+1)*(‖hdecay.toLp (fun x => Real.exp (-d*dist x o))‖+1)*Real.exp (2*a*CF)) d β R S+
        T*(|Real.log (C₀:ℝ)|+|Real.log (C₁:ℝ)|+
          2*((∫ x,Real.exp (-(d*dist x o)) ∂m)+1)+2*d*M)+
        (a*T)*(2*F o-F x₀-F x₁+(L:ℝ)*(2*M+2*r+δ*(D₀+D₁))) := by
  let ν := exponentialMeasure m (fun x => a*F x)
  have hVB : ∀ x,|a*F x| ≤ |a| *CF := fun x => by
    rw [abs_mul]; exact mul_le_mul_of_nonneg_left (hFb x) (abs_nonneg a)
  let h := hrcd.weighted_quadraticCheegerEnergy hfin o hVB
  obtain ⟨Bu,u,hun,hub,hum,hul⟩ := exists_weighted_initial_density hfin o hVB μ₀ hcap
  obtain ⟨μ,hμ,hμE,hμi,hM⟩ := hrcd.weighted_heat_concentration hN hfull hfin o hF.continuous hFb
    ha.le h u hun hum Bu.property hub hr (by rwa [hul]) hB (by rwa [hul]) hd he hT
  obtain ⟨η₀,hη₀E,hη₀cap,hη₀s,hcost₀⟩ := hHess.rcd_localized_plan_law hN hrcd hfull hfin o hF hFb hGb hGc
    ha h u hun hπ₀ hb₀ hg₀ (hul.trans hi₀.symm) hcap₀ hD₀ x₀ hs₀ hl₀ htracks₀
    hd.le hdβ hdecay hlocal hT hTU hδ hsmall
  obtain ⟨η₁,hη₁E,hη₁cap,hη₁s,hcost₁⟩ := hHess.rcd_localized_plan_law hN hrcd hfull hfin o hF hFb hGb hGc
    ha h u hun hπ₁ hb₁ hg₁ (hul.trans hi₁.symm) hcap₁ hD₁ x₁ hs₁ hl₁ htracks₁
    hd.le hdβ hdecay hlocal hT hTU hδ hsmall
  have hRn : 0 ≤ Rd := dist_nonneg.trans hRd
  specialize hcost₀ (midpointDualTest x₀ Rd) (midpointDualTest_compact x₀ hRn) q hq
  specialize hcost₁ (midpointDualTest x₁ Rd) (midpointDualTest_compact x₁ hRn) q hq
  rw [← hμ] at hcost₀ hcost₁
  have Hlow := midpoint_dual_lower x₀ x₁ hRd η₀ η₁ μ hLD₀ hLD₁ hη₀s hη₁s hq
  have H₀ := entropy_exponential_drop_bound hF hFb ha.le hd.le o x₀ η₀ μ hη₀E hμE hμi he hC₀ hη₀cap hη₀s
  have H₁ := entropy_exponential_drop_bound hF hFb ha.le hd.le o x₁ η₁ μ hη₁E hμE hμi he hC₁ hη₁cap hη₁s
  have Hdrop₀ := mul_le_mul_of_nonneg_left H₀ hT
  have Hdrop₁ := mul_le_mul_of_nonneg_left H₁ hT
  have hCG : 0 ≤ CG := (abs_nonneg (G o)).trans (hGb o)
  have hA := localizedActionBound_nonneg (K := K) (c := c) ha.le hCG hT
  have HA₀ := mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right hE₀ (by norm_num : (0:ℝ) ≤ 2)) hA
  have HA₁ := mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right hE₁ (by norm_num : (0:ℝ) ≤ 2)) hA
  refine ⟨∫ x,dist x o ∂(μ:Measure X),integral_nonneg fun x => dist_nonneg,hM,?_⟩
  nlinarith only [Hlow,hcost₀,hcost₁,Hdrop₀,Hdrop₁,HA₀,HA₁]
end WeakHessian

end
end

end OAI
end

section
-- module Solutions.OAIQ52_WH.WeakHessian_Transport_CDPlanLeg
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section
noncomputable section
namespace WeakHessian
open Set Filter MeasureTheory WeakHessianTransport
open scoped Topology ENNReal NNReal

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
variable [CompleteSpace X] [ProperSpace X] [TopologicalSpace.SeparableSpace X]
variable {m : Measure X} [SigmaFinite m]

omit [CompleteSpace X] [ProperSpace X] [TopologicalSpace.SeparableSpace X] [SigmaFinite m] in
lemma exists_small_ball_law (hfull : FullSupport m) (hfin : FiniteOnBoundedSets m)
    (o : X) {r : ℝ} (hr : 0 < r) :
    ∃ μ : ProbabilityMeasure X,∃ B : ℝ≥0,0 < B ∧
      (μ:Measure X) ≤ (B : ℝ≥0∞) • m ∧ (∀ᵐ x ∂(μ:Measure X),dist x o ≤ r) := by
  let S := Metric.ball o r
  have hS : MeasurableSet S := Metric.isOpen_ball.measurableSet
  have hSp : m S ≠ 0 := (hfull S Metric.isOpen_ball ⟨o,Metric.mem_ball_self hr⟩).ne'
  have hSt : m S ≠ ∞ := (hfin S Metric.isBounded_ball).ne
  let ν := (m S)⁻¹ • m.restrict S
  have hp : IsProbabilityMeasure ν := ⟨by
    simp only [ν,Measure.smul_apply,Measure.restrict_apply_univ,smul_eq_mul]
    exact ENNReal.inv_mul_cancel hSp hSt⟩
  let μ : ProbabilityMeasure X := ⟨ν,hp⟩
  refine ⟨μ,((m S)⁻¹).toNNReal,?_,?_,?_⟩
  · exact ENNReal.toNNReal_pos (by simpa only [ne_eq,ENNReal.inv_eq_zero] using hSt)
      (by simpa only [ne_eq,ENNReal.inv_eq_top] using hSp)
  · rw [ENNReal.coe_toNNReal (by simpa only [ne_eq,ENNReal.inv_eq_top] using hSp)]
    change (m S)⁻¹ • m.restrict S ≤ (m S)⁻¹ • m
    gcongr
    exact Measure.restrict_le_self
  · exact (Measure.ae_smul_measure (ae_restrict_mem hS) ((m S)⁻¹)).mono fun x hx => hx.le

omit [CompleteSpace X] in
lemma CurvatureDimension.exists_plan_leg {K N : ℝ} (hN : 1 < N)
    (hCD : CurvatureDimension m K N) (hfin : FiniteOnBoundedSets m)
    (μ₀ μ₁ : ProbabilityMeasure X) (x₀ x₁ : X) {r : ℝ} (hr : 0 ≤ r)
    (hs₀ : ∀ᵐ x ∂(μ₀:Measure X),dist x x₀ ≤ r)
    (hs₁ : ∀ᵐ x ∂(μ₁:Measure X),dist x x₁ ≤ r)
    {B₀ B₁ : ℝ≥0} (hB₀ : 0 < B₀) (hB₁ : 0 < B₁)
    (hb₀ : (μ₀:Measure X) ≤ (B₀:ℝ≥0∞) • m)
    (hb₁ : (μ₁:Measure X) ≤ (B₁:ℝ≥0∞) • m) :
    ∃ π : Measure (Curve X),∃ C : ℝ≥0,0 < C ∧ IsTestPlan m π ∧ BoundedTracks π ∧
      (∀ᵐ γ ∂π,IsGeodesic γ) ∧
      π.map (fun γ => γ timeZero) = (μ₀:Measure X) ∧
      π.map (fun γ => γ timeOne) = (μ₁:Measure X) ∧
      (∀ t : Time,π.map (fun γ => γ t) ≤ (C:ℝ≥0∞) • m) ∧
      (∀ᵐ γ ∂π,dist (γ timeZero) x₀ ≤ r ∧ dist (γ timeOne) x₁ ≤ r ∧
        dist (γ timeZero) (γ timeOne) ≤ dist x₀ x₁+2*r) ∧
      planKineticCost π ≤ (dist x₀ x₁+2*r)^2 := by
  let R : ℝ≥0 := ⟨dist x₀ x₁+r+1,by positivity⟩
  let B : ℝ≥0 := B₀+B₁
  have hB : 0 < B := add_pos hB₀ hB₁
  have hb0 : (μ₀:Measure X) ≤ (B:ℝ≥0∞) • m := hb₀.trans (by
    gcongr; exact le_add_of_nonneg_right (show 0 ≤ B₁ from zero_le))
  have hb1 : (μ₁:Measure X) ≤ (B:ℝ≥0∞) • m := hb₁.trans (by
    gcongr; exact le_add_of_nonneg_left (show 0 ≤ B₀ from zero_le))
  have hS0 : (μ₀:Measure X) (Metric.closedBall x₀ (R:ℝ))ᶜ = 0 := ae_iff.mp
    (hs₀.mono fun x hx => by change dist x x₀ ≤ dist x₀ x₁+r+1; linarith [dist_nonneg (x := x₀) (y := x₁)])
  have hS1 : (μ₁:Measure X) (Metric.closedBall x₀ (R:ℝ))ᶜ = 0 := ae_iff.mp
    (hs₁.mono fun x hx => by
      change dist x x₀ ≤ dist x₀ x₁+r+1
      have H := dist_triangle x x₁ x₀
      rw [dist_comm x₁ x₀] at H; linarith)
  obtain ⟨π,hπ,hbt,hg,ho,_,_,hcap⟩ := hCD.exists_entropy_testPlan hN hfin μ₀ μ₁ x₀ R
    hS0 hS1 (by exact_mod_cast hB.ne') ENNReal.coe_ne_top hb0 hb1
  let C : ℝ≥0 := B*(Real.exp (4*compressionRate K N*R)).toNNReal
  have hC : 0 < C := mul_pos hB (Real.toNNReal_pos.mpr (Real.exp_pos _))
  have h0 : (π:Measure (Curve X)).map (fun γ => γ timeZero) = (μ₀:Measure X) := by
    simpa only [endpointCoupling,Measure.map_map measurable_fst
      ((continuous_eval_const timeZero).measurable.prodMk (continuous_eval_const timeOne).measurable),Function.comp_def]
      using ho.1.1
  have h1 : (π:Measure (Curve X)).map (fun γ => γ timeOne) = (μ₁:Measure X) := by
    simpa only [endpointCoupling,Measure.map_map measurable_snd
      ((continuous_eval_const timeZero).measurable.prodMk (continuous_eval_const timeOne).measurable),Function.comp_def]
      using ho.1.2
  have ht : ∀ᵐ γ ∂(π:Measure (Curve X)),dist (γ timeZero) x₀ ≤ r ∧
      dist (γ timeOne) x₁ ≤ r ∧ dist (γ timeZero) (γ timeOne) ≤ dist x₀ x₁+2*r := by
    have H0 := ae_of_ae_map (μ := (π:Measure (Curve X))) (f := fun γ => γ timeZero)
      (continuous_eval_const timeZero).measurable.aemeasurable (h0.symm ▸ hs₀)
    have H1 := ae_of_ae_map (μ := (π:Measure (Curve X))) (f := fun γ => γ timeOne)
      (continuous_eval_const timeOne).measurable.aemeasurable (h1.symm ▸ hs₁)
    filter_upwards [H0,H1] with γ hγ0 hγ1
    refine ⟨hγ0,hγ1,?_⟩
    have H := dist_triangle (γ timeZero) x₀ (γ timeOne)
    have H' := dist_triangle x₀ x₁ (γ timeOne)
    rw [dist_comm x₁ (γ timeOne)] at H'
    linarith
  refine ⟨π,C,hC,hπ,hbt,hg,h0,h1,?_,ht,?_⟩
  · intro t
    simpa only [C,interpolation,ENNReal.coe_mul,ENNReal.ofReal] using hcap t
  · have hi : Integrable (fun γ : Curve X => dist (γ timeZero) (γ timeOne)^2) (π:Measure (Curve X)) :=
      Integrable.of_bound (by fun_prop) ((dist x₀ x₁+2*r)^2) (ht.mono fun γ hγ => by
        rw [Real.norm_of_nonneg (sq_nonneg _)]
        exact pow_le_pow_left₀ dist_nonneg hγ.2.2 2)
    have H := integral_mono_ae hi (integrable_const ((dist x₀ x₁+2*r)^2))
      (ht.mono fun γ hγ => pow_le_pow_left₀ dist_nonneg hγ.2.2 2)
    simpa only [planKineticCost,integral_const,probReal_univ,one_smul] using H

end WeakHessian

end
end

end OAI
end

section
-- module Solutions.OAIQ52_WH.WeakHessian_Geodesics_LocalMidpoint
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section
noncomputable section
namespace WeakHessian
open Set Filter MeasureTheory WeakHessianTransport WeakHessianFunctional
open scoped Topology ENNReal NNReal BoundedContinuousFunction

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
variable [CompleteSpace X] [ProperSpace X] [TopologicalSpace.SeparableSpace X]
variable {m : Measure X} [SigmaFinite m]

omit [MeasurableSpace X] [BorelSpace X] [CompleteSpace X] [ProperSpace X]
    [TopologicalSpace.SeparableSpace X] in
lemma geodesic_dist_initial_le {γ : Curve X} (hγ : IsGeodesic γ) (t : Time) :
    dist (γ t) (γ timeZero) ≤ dist (γ timeZero) (γ timeOne) := by
  rw [hγ t timeZero]
  change |(t:ℝ)-0| *dist (γ timeZero) (γ timeOne) ≤ _
  rw [sub_zero,abs_of_nonneg t.property.1]
  exact mul_le_of_le_one_left dist_nonneg t.property.2

lemma WeakHessianUpperBound.rcd_local_midpoint {K N : ℝ}
    (hN : 1 < N) (hrcd : RCD m K N) (hfull : FullSupport m) (hfin : FiniteOnBoundedSets m)
    {F G : X → ℝ} (hHess : WeakHessianUpperBound m F G)
    {L : ℝ≥0} (hF : LipschitzWith L F) {CF CG : ℝ} (hFb : ∀ x,|F x| ≤ CF)
    (hGb : ∀ x,|G x| ≤ CG) (hGc : Continuous G)
    (σ : Curve X) (hσ : IsGeodesic σ) {R c : ℝ}
    (hR : 0 < R) (hshort : dist (σ timeZero) (σ timeOne) < R)
    (hlocal : ∀ x,dist x (σ timeHalf) < R → G x ≤ c) :
    (F (σ timeZero)+F (σ timeOne))/2-c/8*dist (σ timeZero) (σ timeOne)^2 ≤ F (σ timeHalf) := by
  let o := σ timeHalf
  let x₀ := σ timeZero
  let x₁ := σ timeOne
  let D := dist x₀ x₁
  have hd0 : dist o x₀ = D/2 := by
    change dist (σ timeHalf) (σ timeZero) = _
    rw [hσ timeHalf timeZero]
    norm_num [timeHalf,timeZero,D,x₀,x₁]; ring
  have hd1 : dist o x₁ = D/2 := by
    change dist (σ timeHalf) (σ timeOne) = _
    rw [hσ timeHalf timeOne]
    norm_num [timeHalf,timeOne,D,x₀,x₁]; ring
  obtain ⟨LD₀,hLD₀⟩ := boundedHopfMap_lipschitz (midpointDualTest x₀ D) zero_lt_one
  obtain ⟨LD₁,hLD₁⟩ := boundedHopfMap_lipschitz (midpointDualTest x₁ D) zero_lt_one
  apply midpoint_bound_of_local_two_leg_approx (LD := (LD₀:ℝ)+(LD₁:ℝ))
    (J := 2*(‖midpointDualTest x₀ D‖+‖midpointDualTest x₁ D‖)) (CG := CG) (CF := CF) (L := (L:ℝ))
  have hgap : 0 < R-3*R/4 := by linarith
  filter_upwards [eventually_local_scaling_admissible c CG CF hgap,self_mem_nhdsWithin] with s hadm hs
  have hsp : 0 < s := hs
  filter_upwards [(eventually_lt_nhds (show (0:ℝ) < R/12 by positivity)).filter_mono nhdsWithin_le_nhds,
    self_mem_nhdsWithin] with r hrR hr
  have hrp : 0 < r := hr
  intro δ q hδ hq
  obtain ⟨μ,B,hB,hμcap,hμs⟩ := exists_small_ball_law hfull hfin o hrp
  obtain ⟨μ₀,B₀,hB₀,hμ₀cap,hμ₀s⟩ := exists_small_ball_law hfull hfin x₀ hrp
  obtain ⟨μ₁,B₁,hB₁,hμ₁cap,hμ₁s⟩ := exists_small_ball_law hfull hfin x₁ hrp
  obtain ⟨π₀,C₀,hC₀,hπ₀,hb₀,hg₀,hi₀,_,hcap₀,ht₀,hE₀⟩ :=
    hrcd.1.exists_plan_leg hN hfin μ μ₀ o x₀ hrp.le hμs hμ₀s hB hB₀ hμcap hμ₀cap
  obtain ⟨π₁,C₁,hC₁,hπ₁,hb₁,hg₁,hi₁,_,hcap₁,ht₁,hE₁⟩ :=
    hrcd.1.exists_plan_leg hN hfin μ μ₁ o x₁ hrp.le hμs hμ₁s hB hB₁ hμcap hμ₁cap
  have htrack₀ : ∀ᵐ γ ∂π₀,∀ t : Time,dist (γ t) o < 3*R/4 := by
    filter_upwards [hg₀,ht₀] with γ hγ hγt t
    have H := dist_triangle (γ t) (γ timeZero) o
    have H' := geodesic_dist_initial_le hγ t
    rw [hd0] at hγt
    change D < R at hshort
    linarith [hγt.1,hγt.2.2]
  have htrack₁ : ∀ᵐ γ ∂π₁,∀ t : Time,dist (γ t) o < 3*R/4 := by
    filter_upwards [hg₁,ht₁] with γ hγ hγt t
    have H := dist_triangle (γ t) (γ timeZero) o
    have H' := geodesic_dist_initial_le hγ t
    rw [hd1] at hγt
    change D < R at hshort
    linarith [hγt.1,hγt.2.2]
  obtain ⟨d,hd,he,hdecay,_,_,_⟩ := hrcd.1.exists_strong_entropy_confinement hN hfull hfin o
  have hdecay' : MemLp (fun x => Real.exp (-d*dist x o)) 2 m := by simpa only [neg_mul] using hdecay
  let E := ∫ x,Real.exp (-(d*dist x o)) ∂m
  let Q₀ := ((C₀:ℝ)+1)*(‖hdecay'.toLp (fun x => Real.exp (-d*dist x o))‖+1)
  let Q₁ := ((C₁:ℝ)+1)*(‖hdecay'.toLp (fun x => Real.exp (-d*dist x o))‖+1)
  have hD : 0 ≤ D/2+2*r := by dsimp [D]; positivity
  have H := vanishing_diffusion_local_two_leg
    (Z := D^2/4-((LD₀:ℝ)+(LD₁:ℝ))*(r+δ*(D/2+2*r))-
      2*(‖midpointDualTest x₀ D‖+‖midpointDualTest x₁ D‖)*q)
    (E := (D/2+2*r)^2) (s := s) (A := 4*r^2+16*s*CF)
    (B := 8*(|Real.log (B:ℝ)|+E+1)) (C := |Real.log (C₀:ℝ)|+|Real.log (C₁:ℝ)|+2*(E+1))
    (d := d) (f := 2*F o-F x₀-F x₁) (L := (L:ℝ)) (R := 2*r+δ*(D+4*r))
    hsp.le hd.le L.property (localizedActionBound_scaling_limit K c CG hsp.le)
    (curvatureTailBound_scaling_limit K c CG CF s (hopfUniformLip (midpointDualTest x₀ D) q) Q₀ d R (3*R/4) hadm.2)
    (curvatureTailBound_scaling_limit K c CG CF s (hopfUniformLip (midpointDualTest x₁ D) q) Q₁ d R (3*R/4) hadm.2) ?_
  · convert H using 1
    all_goals try with_reducible_and_instances rfl
    dsimp [o,x₀,x₁,D]
    ring
  · filter_upwards [localized_small_scaled_eventually (K := K) hadm.1,self_mem_nhdsWithin] with T hsmall hT
    have hTp : 0 < T := hT
    have hβ : d ≤ d+(R-3*R/4)/(4*T) := by linarith [div_nonneg hgap.le (by positivity : (0:ℝ) ≤ 4*T)]
    obtain ⟨M,hM0,hM,hcomp⟩ := hHess.rcd_common_local_heat_legs hN hrcd hfull hfin hF hFb hGb hGc
      o x₀ x₁ μ hrp.le hμs hB hμcap hd he hdecay' hC₀ hC₁ hπ₀ hπ₁ hb₀ hb₁ hg₀ hg₁ hi₀ hi₁ hcap₀ hcap₁
      (D₀ := D/2+2*r) (D₁ := D/2+2*r) hD hD
      (ht₀.mono fun γ hγ => hγ.2.1) (ht₁.mono fun γ hγ => hγ.2.1)
      (by simpa only [hd0] using ht₀.mono fun γ hγ => hγ.2.2)
      (by simpa only [hd1] using ht₁.mono fun γ hγ => hγ.2.2)
      (by simpa only [hd0] using hE₀) (by simpa only [hd1] using hE₁)
      htrack₀ htrack₁ hlocal (Rd := D) le_rfl hLD₀ hLD₁
      (a := s/T) (div_pos hsp hTp) hTp.le (by linarith : T < 2*T) hδ hq hβ hsmall
    rw [div_mul_cancel₀ s hTp.ne'] at hcomp
    rw [mul_div_cancel₀ s hTp.ne'] at hM
    refine ⟨M,hM0,?_,?_⟩
    · convert hM using 1
      all_goals try with_reducible_and_instances rfl
      dsimp [E]
      ring
    · convert hcomp using 1 <;> dsimp [D,E,Q₀,Q₁] <;> ring
end WeakHessian

end
end

end OAI
end

section
-- module Solutions.OAIQ52_WH.WeakHessian_Calculus_LocalDistribution
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section
noncomputable section
namespace WeakHessian
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
variable [CompleteSpace X] [ProperSpace X] [TopologicalSpace.SeparableSpace X]

omit [MeasurableSpace X] [BorelSpace X] [CompleteSpace X]
    [TopologicalSpace.SeparableSpace X] in
lemma local_midpoint_implies_curve_bound {F G : X → ℝ} (hFc : Continuous F) (hGc : Continuous G)
    (hmid : ∀ γ : Curve X,IsGeodesic γ → ∀ R c : ℝ,0 < R →
      dist (γ timeZero) (γ timeOne) < R →
      (∀ z,dist z (γ timeHalf) < R → G z ≤ c) →
      (F (γ timeZero)+F (γ timeOne))/2-c/8*dist (γ timeZero) (γ timeOne)^2 ≤ F (γ timeHalf))
    (σ : Curve X) (hσ : IsGeodesic σ) : CurveSecondDerivativeBound F G σ := by
  let D := dist (σ timeZero) (σ timeOne)
  have hD : 0 ≤ D := dist_nonneg
  have hσr : Continuous (evalReal σ) :=
    continuous_evalReal.comp (continuous_const.prodMk continuous_id)
  have hlocal : ∀ ε : ℝ,0 < ε → ∃ δ : ℝ,0 < δ ∧ ∀ h : ℝ,0 < h → h < δ →
      ∀ x : ℝ,x-h ∈ Ioo (0:ℝ) 1 → x+h ∈ Ioo (0:ℝ) 1 →
        secondDifference (F ∘ evalReal σ) h x ≤ D^2*G (evalReal σ x)+ε := by
    intro ε hε
    let e := ε/(D^2+1)
    have he : 0 < e := by dsimp [e]; positivity
    obtain ⟨η,hη,hηs⟩ := Metric.uniformContinuousOn_iff.mp
      ((isCompact_closedBall (σ timeZero) (D+1)).uniformContinuousOn_of_continuous hGc.continuousOn) e he
    let R := min η 1
    have hR : 0 < R := lt_min hη zero_lt_one
    refine ⟨R/(2*(D+1)),by positivity,?_⟩
    intro h hh hhR x hm hp
    have hx : x ∈ Icc (0:ℝ) 1 := by constructor <;> linarith [hm.1,hp.2]
    let u : Time := ⟨x-h,hm.1.le,hm.2.le⟩
    let v : Time := ⟨x+h,hp.1.le,hp.2.le⟩
    let γ := restrictCurve u v σ
    have hγ : IsGeodesic γ := hσ.restrictCurve u v
    have hg0 : γ timeZero = evalReal σ (x-h) := by
      rw [restrictCurve_zero]
      congr 1
      apply Subtype.ext
      exact (clampTime_of_mem ⟨hm.1.le,hm.2.le⟩).symm
    have hg1 : γ timeOne = evalReal σ (x+h) := by
      rw [restrictCurve_one]
      congr 1
      apply Subtype.ext
      exact (clampTime_of_mem ⟨hp.1.le,hp.2.le⟩).symm
    have hgm : γ timeHalf = evalReal σ x := by
      change σ (affineTime u v timeHalf) = σ (clampTime x)
      congr 1
      apply Subtype.ext
      rw [clampTime_of_mem hx]
      dsimp [affineTime,u,v,timeHalf]
      ring
    have hlen : dist (γ timeZero) (γ timeOne) = 2*h*D := by
      rw [restrictCurve_zero,restrictCurve_one,hσ u v]
      change |(x-h)-(x+h)| *D = 2*h*D
      rw [abs_of_nonpos (by linarith)]
      ring
    have hshort : dist (γ timeZero) (γ timeOne) < R := by
      rw [hlen]
      have H := (lt_div_iff₀ (by positivity : (0:ℝ) < 2*(D+1))).mp hhR
      nlinarith
    have hnear : ∀ z,dist z (γ timeHalf) < R → G z ≤ G (evalReal σ x)+e := by
      intro z hz
      rw [hgm] at hz
      have hcenter : dist (evalReal σ x) (σ timeZero) ≤ D :=
        geodesic_dist_initial_le hσ (clampTime x)
      have hzB : z ∈ Metric.closedBall (σ timeZero) (D+1) := by
        apply Metric.mem_closedBall.mpr
        have HR : R ≤ 1 := min_le_right η 1
        have H := dist_triangle z (evalReal σ x) (σ timeZero)
        linarith
      have hxB : evalReal σ x ∈ Metric.closedBall (σ timeZero) (D+1) := by
        apply Metric.mem_closedBall.mpr
        linarith
      have H := hηs z hzB (evalReal σ x) hxB (hz.trans_le (min_le_left η 1))
      rw [Real.dist_eq] at H
      linarith [(abs_lt.mp H).2]
    have H := hmid γ hγ R (G (evalReal σ x)+e) hR hshort hnear
    rw [hlen,hg0,hg1,hgm] at H
    have H' : secondDifference (F ∘ evalReal σ) h x ≤ D^2*(G (evalReal σ x)+e) := by
      apply (div_le_iff₀ (sq_pos_of_pos hh)).mpr
      change F (evalReal σ (x+h))+F (evalReal σ (x-h))-2*F (evalReal σ x) ≤ _
      nlinarith only [H]
    apply H'.trans
    have hE : D^2*e ≤ ε := by
      dsimp [e]
      rw [← mul_div_assoc]
      apply (div_le_iff₀ (by positivity : (0:ℝ) < D^2+1)).mpr
      nlinarith
    nlinarith only [hE]
  intro φ hφ hc hs hnn
  have H := setIntegral_second_deriv_le_of_local_differences (hFc.comp hσr)
    (show Continuous (fun t => D^2*G (evalReal σ t)) from continuous_const.mul (hGc.comp hσr)) hlocal
    (hφ.of_le (WithTop.coe_le_coe.mpr le_top)) hc hs hnn
  change (∫ t in Icc (0:ℝ) 1,F (evalReal σ t)*deriv (deriv φ) t) ≤
    D^2*(∫ t in Icc (0:ℝ) 1,G (evalReal σ t)*φ t)
  convert H using 1
  · rfl
  · simp_rw [mul_assoc]
    rw [integral_const_mul]
end WeakHessian

end
end

end OAI
end

section
-- module Solutions.OAIQ52_WH.WeakHessian_Main
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

noncomputable section
attribute [local instance] Classical.propDecidable
namespace WeakHessian
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]

theorem every_geodesic_oai [CompleteSpace X] [TopologicalSpace.SeparableSpace X]
    (m : Measure X) (K N : ℝ) (hN : 1 < N)
    (hfull : FullSupport m) (hfinite : FiniteOnBoundedSets m) (hrcd : RCD m K N)
    (F G : X → ℝ) (hFbound : BoundedFunction F) (hFlip : GloballyLipschitz F)
    (hGbound : BoundedFunction G) (hGcont : Continuous G)
    (hHess : WeakHessianUpperBound m F G)
    (σ : Curve X) (hσ : IsGeodesic σ) : CurveSecondDerivativeBound F G σ := by
  let : ProperSpace X := properSpace_of_cd hN hrcd.1 hfull hfinite
  let : SigmaFinite m := sigmaFinite_of_finiteOnBoundedSets m hfinite (σ timeZero)
  obtain ⟨CF,hCF⟩ := hFbound
  obtain ⟨L,hL⟩ := hFlip
  obtain ⟨CG,hCG⟩ := hGbound
  apply local_midpoint_implies_curve_bound hL.continuous hGcont _ σ hσ
  intro γ hγ R c hR hshort hlocal
  exact hHess.rcd_local_midpoint hN hrcd hfull hfinite hL hCF hCG hGcont γ hγ hR hshort hlocal

end WeakHessian

end
end

end OAI
end

theorem solution.{u_1} : type_of% @OAI.WeakHessian.every_geodesic_oai.{u_1} := @OAI.WeakHessian.every_geodesic_oai.{u_1}
