-- Prove2me | solution 1 for OrderSelProphet.Kernel.lemma_F_2
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Xeroth
-- created : 2026-11-24T23:24:32.895794+00:00
-- url     : https://prove2.me/submissions/63d49493-0591-45c3-ba64-431eb630e399
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_OrderSelProphet_Kernel_Certificate
import Theorems.Thm_OrderSelProphet_Kernel_lemma_4_2
import Theorems.Thm_OrderSelProphet_Kernel_lemma_F_1

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ENNReal

namespace OrderSelProphet.Kernel

lemma F2_Gamma1_mem : Gamma1 ∈ Ioo (0 : ℝ) 1 := by
  unfold Gamma1; constructor <;> norm_num

lemma F2_upperInv_nonneg (A : ℝ → ℝ) (b : ℝ) : 0 ≤ upperInv A b :=
  Real.sSup_nonneg (fun _ hx => hx.1.1)

lemma F2_upperInv_le_one (A : ℝ → ℝ) (b : ℝ) : upperInv A b ≤ 1 :=
  Real.sSup_le (fun _ hx => hx.1.2) zero_le_one

lemma F2_alloc_sub_le (hK : IsAllocationKernel K1) (lam : Profile) {t t' : ℝ} (ht : 0 < t)
    (htt : t ≤ t') (ht' : t' ≤ 1) :
    allocK K1 lam.1 t' - allocK K1 lam.1 t ≤ t' - t := by
  obtain ⟨_, _, hae, hint⟩ := hK
  have hKi : ∀ s, 0 < s → s ≤ 1 → IntervalIntegrable (fun u => K1 s u) volume 0 1 := by
    intro s hs hs1
    by_contra h
    have := hint s ⟨hs.le, hs1⟩
    rw [intervalIntegral.integral_undef h] at this
    linarith
  have hlK : ∀ s, 0 < s → s ≤ 1 →
      IntervalIntegrable (fun u => lam.1 u * K1 s u) volume 0 1 := by
    intro s hs hs1
    have h1 := hKi s hs hs1
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one] at h1 ⊢
    refine Integrable.bdd_mul (c := 1) h1 lam.2.1.aestronglyMeasurable ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with u hu
    have := lam.2.2 u ⟨hu.1.le, hu.2⟩
    rw [Real.norm_eq_abs, abs_le]; constructor <;> linarith [this.1, this.2]
  have ht0 : 0 < t' := lt_of_lt_of_le ht htt
  have hsub : t' - t = ∫ u in (0 : ℝ)..1, (K1 t' u - K1 t u) := by
    rw [intervalIntegral.integral_sub (hKi t' ht0 ht') (hKi t ht (htt.trans ht')),
      hint t' ⟨ht0.le, ht'⟩, hint t ⟨ht.le, htt.trans ht'⟩]
  unfold allocK
  rw [← intervalIntegral.integral_sub (hlK t' ht0 ht') (hlK t ht (htt.trans ht')), hsub]
  apply intervalIntegral.integral_mono_ae_restrict zero_le_one
    ((hlK t' ht0 ht').sub (hlK t ht (htt.trans ht')))
    ((hKi t' ht0 ht').sub (hKi t ht (htt.trans ht')))
  filter_upwards [hae, ae_restrict_mem measurableSet_Icc] with u hu hmem
  have hm := hu.1 ⟨ht.le, htt.trans ht'⟩ ⟨ht0.le, ht'⟩ htt
  have hl := lam.2.2 u hmem
  simp only at hm ⊢
  nlinarith [hl.1, hl.2]

lemma F2_deriv_alloc_le_one (hK : IsAllocationKernel K1) (lam : Profile) {t : ℝ}
    (ht : t ∈ Ioo (0 : ℝ) 1) : deriv (allocK K1 lam.1) t ≤ 1 := by
  by_cases hd : DifferentiableAt ℝ (allocK K1 lam.1) t
  · have hmono : MonotoneOn (fun s => s - allocK K1 lam.1 s) (Ioo 0 1) := by
      intro a ha b hb hab
      have := F2_alloc_sub_le hK lam ha.1 hab hb.2.le
      simp only
      linarith
    have h1 := hmono.derivWithin_nonneg (x := t)
    have hh : HasDerivAt (fun s => s - allocK K1 lam.1 s) (1 - deriv (allocK K1 lam.1) t) t :=
      (hasDerivAt_id' t).sub hd.hasDerivAt
    rw [derivWithin_of_isOpen isOpen_Ioo ht, hh.deriv] at h1
    linarith
  · rw [deriv_zero_of_not_differentiableAt hd]; norm_num

lemma F2_tR_hasStrictDerivAt (r : ℝ) : HasStrictDerivAt tR (r * Real.exp (-r)) r := by
  have h1 : HasStrictDerivAt (fun s : ℝ => 1 + s) 1 r := (hasStrictDerivAt_id r).const_add 1
  have h2 : HasStrictDerivAt (fun s : ℝ => Real.exp (-s)) (Real.exp (-r) * (-1)) r :=
    (Real.hasStrictDerivAt_exp (-r)).comp r (hasStrictDerivAt_neg r)
  have h3 := (h1.mul h2).const_sub 1
  exact h3.congr_deriv (by ring)

lemma F2_tR_zero : tR 0 = 0 := by simp [tR]

lemma F2_tR_strictMonoOn : StrictMonoOn tR (Ici 0) := by
  apply strictMonoOn_of_deriv_pos (convex_Ici 0)
  · exact fun x _ => (F2_tR_hasStrictDerivAt x).hasDerivAt.continuousAt.continuousWithinAt
  · intro x hx
    rw [interior_Ici] at hx
    rw [(F2_tR_hasStrictDerivAt x).hasDerivAt.deriv]
    exact mul_pos hx (Real.exp_pos _)

lemma F2_tR_tendsto : Tendsto tR atTop (𝓝 1) := by
  have h1 := Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 1
  have h2 : Tendsto (fun x : ℝ => Real.exp (-x)) atTop (𝓝 0) :=
    Real.tendsto_exp_atBot.comp tendsto_neg_atTop_atBot
  have h3 := (h2.add h1).const_sub 1
  simp only [pow_one, add_zero, sub_zero] at h3
  convert h3 using 2 with x
  unfold tR; ring

lemma F2_tR_image : tR '' Ioi 0 = Ioo 0 1 := by
  ext t
  constructor
  · rintro ⟨r, hr, rfl⟩
    constructor
    · have := F2_tR_strictMonoOn (mem_Ici.2 le_rfl) (mem_Ici.2 (le_of_lt hr)) hr
      rwa [F2_tR_zero] at this
    · unfold tR
      have : 0 < (1 + r) * Real.exp (-r) := mul_pos (by linarith [hr.out]) (Real.exp_pos _)
      linarith
  · rintro ⟨h0, h1⟩
    obtain ⟨N, hN⟩ := (eventually_gt_atTop 0).and
      (F2_tR_tendsto.eventually (lt_mem_nhds h1)) |>.exists
    have hc : ContinuousOn tR (Icc 0 N) :=
      fun x _ => (F2_tR_hasStrictDerivAt x).hasDerivAt.continuousAt.continuousWithinAt
    have := intermediate_value_Ioo hN.1.le hc
    rw [F2_tR_zero] at this
    obtain ⟨r, hr, hrt⟩ := this ⟨h0, hN.2⟩
    exact ⟨r, hr.1, hrt⟩

lemma F2_deriv_comp_tR (B : ℝ → ℝ) {r : ℝ} (hr : 0 < r) :
    deriv (fun s => B (tR s)) r = deriv B (tR r) * (r * Real.exp (-r)) := by
  have htR := F2_tR_hasStrictDerivAt r
  have hne : r * Real.exp (-r) ≠ 0 := (mul_pos hr (Real.exp_pos _)).ne'
  by_cases hB : DifferentiableAt ℝ B (tR r)
  · exact (hB.hasDerivAt.comp r htR.hasDerivAt).deriv
  · have hnd : ¬ DifferentiableAt ℝ (fun s => B (tR s)) r := by
      intro hc
      apply hB
      have hg := htR.to_localInverse hne
      have hl := htR.eventually_left_inverse hne
      have hr' := htR.eventually_right_inverse hne
      have hgr := hl.self_of_nhds
      have hc' := hc.hasDerivAt
      rw [← hgr] at hc'
      have hcomp := hc'.comp (tR r) hg.hasDerivAt
      refine (hcomp.congr_of_eventuallyEq ?_).differentiableAt
      filter_upwards [hr'] with x hx
      simp only [Function.comp, hx]
    rw [deriv_zero_of_not_differentiableAt hB, deriv_zero_of_not_differentiableAt hnd, zero_mul]

lemma F2_one_sub_tR (r : ℝ) :
    1 - Gamma1 * tR r = Gamma1 * Real.exp (-r) * Dc r := by
  unfold tR Dc DG cG
  have hG : Gamma1 ≠ 0 := F2_Gamma1_mem.1.ne'
  rw [Real.exp_neg]
  have hE : Real.exp r ≠ 0 := (Real.exp_pos r).ne'
  field_simp
  ring

lemma F2_Dc_pos {r : ℝ} (hr : 0 ≤ r) : 0 < Dc r := by
  unfold Dc DG cG
  have : 0 < (1 - Gamma1) / Gamma1 := div_pos (by linarith [F2_Gamma1_mem.2]) F2_Gamma1_mem.1
  have := Real.exp_pos r
  positivity

lemma F2_cov (lam : Profile) :
    ∫ r in Ioi (0 : ℝ), sigmaC lam.1 r * (r - kRate lam.1 r) * Rc lam.1 r / Dc r ^ 2
      = Gamma1 ^ 2 * ∫ t in (0 : ℝ)..1, SK Gamma1 K1 lam.1 t * (1 - yK K1 lam.1 t) *
          (1 - deriv (allocK K1 lam.1) t) / (1 - Gamma1 * t) ^ 2 := by
  rw [intervalIntegral.integral_of_le zero_le_one, integral_Ioc_eq_integral_Ioo, ← F2_tR_image,
    integral_image_eq_integral_abs_deriv_smul measurableSet_Ioi
      (fun x _ => (F2_tR_hasStrictDerivAt x).hasDerivAt.hasDerivWithinAt)
      (F2_tR_strictMonoOn.injOn.mono Ioi_subset_Ici_self),
    ← integral_const_mul]
  refine setIntegral_congr_fun measurableSet_Ioi (fun r hr => ?_)
  have hr0 : 0 < r := hr
  simp only [smul_eq_mul]
  rw [F2_one_sub_tR, abs_of_pos (mul_pos hr0 (Real.exp_pos _))]
  unfold kRate Rc sigmaC Yc
  rw [F2_deriv_comp_tR _ hr0, Real.exp_neg]
  have hG : Gamma1 ≠ 0 := F2_Gamma1_mem.1.ne'
  have hE : Real.exp r ≠ 0 := (Real.exp_pos r).ne'
  have hD : Dc r ≠ 0 := (F2_Dc_pos hr0.le).ne'
  field_simp

theorem F2_part2 (lam : Profile) :
    auxLoad lam.1 = ENNReal.ofReal (Gamma1 + ∫ r in Ioi (0 : ℝ),
        sigmaC lam.1 r * (r - kRate lam.1 r) * Rc lam.1 r / Dc r ^ 2) := by
  have hK : IsAllocationKernel K1 := lemma_F_1.2.2.2.1
  have hG := F2_Gamma1_mem
  have hI : 0 ≤ ∫ t in (0 : ℝ)..1, SK Gamma1 K1 lam.1 t * (1 - yK K1 lam.1 t) *
      (1 - deriv (allocK K1 lam.1) t) / (1 - Gamma1 * t) ^ 2 := by
    rw [intervalIntegral.integral_of_le zero_le_one, integral_Ioc_eq_integral_Ioo]
    refine setIntegral_nonneg measurableSet_Ioo (fun t ht => ?_)
    have h1 : 0 ≤ SK Gamma1 K1 lam.1 t := (Real.exp_pos _).le
    have h2 : 0 ≤ 1 - yK K1 lam.1 t := by
      have := F2_upperInv_le_one (areaP lam.1) (allocK K1 lam.1 t)
      unfold yK threshold; linarith
    have h3 : 0 ≤ 1 - deriv (allocK K1 lam.1) t := by
      linarith [F2_deriv_alloc_le_one hK lam ht]
    positivity
  have hX : 0 ≤ Gamma1 * (1 - yK K1 lam.1 0) + Gamma1 ^ 2 * ∫ t in (0 : ℝ)..1,
      SK Gamma1 K1 lam.1 t * (1 - yK K1 lam.1 t) *
        (1 - deriv (allocK K1 lam.1) t) / (1 - Gamma1 * t) ^ 2 := by
    have := F2_upperInv_le_one (areaP lam.1) (allocK K1 lam.1 0)
    have h0 : 0 ≤ 1 - yK K1 lam.1 0 := by unfold yK threshold; linarith
    have := hG.1
    positivity
  have hY : 0 ≤ Gamma1 * Yc lam.1 0 :=
    mul_nonneg hG.1.le (F2_upperInv_nonneg _ _)
  unfold auxLoad
  rw [lemma_4_2 hG K1 hK lam, ← ENNReal.ofReal_add hX hY, F2_cov]
  congr 1
  unfold Yc
  rw [F2_tR_zero]
  ring

theorem F2_part1 (lam : Profile) : loadK Gamma1 K1 lam.1 ≤ auxLoad lam.1 := by
  unfold auxLoad
  exact le_self_add

end OrderSelProphet.Kernel

theorem solution (lam : OrderSelProphet.Kernel.Profile) :
    OrderSelProphet.Kernel.loadK OrderSelProphet.Kernel.Gamma1 OrderSelProphet.Kernel.K1 lam.1
        ≤ OrderSelProphet.Kernel.auxLoad lam.1 ∧
      OrderSelProphet.Kernel.auxLoad lam.1 = ENNReal.ofReal (OrderSelProphet.Kernel.Gamma1 +
        ∫ r in Ioi (0 : ℝ), OrderSelProphet.Kernel.sigmaC lam.1 r *
          (r - OrderSelProphet.Kernel.kRate lam.1 r) * OrderSelProphet.Kernel.Rc lam.1 r /
            OrderSelProphet.Kernel.Dc r ^ 2) :=
  ⟨OrderSelProphet.Kernel.F2_part1 lam, OrderSelProphet.Kernel.F2_part2 lam⟩
