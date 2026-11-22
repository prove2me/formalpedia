-- Prove2me | solution 1 for PHarmWeakGradClassical
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T20:11:27.495059+00:00
-- url     : https://prove2.me/submissions/5f1608ab-8639-40be-98b8-d4e8699a8624

import Definitions.Def_PHigherOrder_IsPHarm
import Definitions.Def_PHigherOrder_TestFunctionGradientIntegral
import Definitions.Def_PHigherOrder_VanishingOffTsupport
import Definitions.Def_PHigherOrder_PHarmWeakGradClassical
import Theorems.Thm_TestFunctionGradientIntegral
import Theorems.Thm_VanishingOffTsupport


set_option autoImplicit false

theorem _root_.solution (p : ℝ) (hp : 1 < p) (Ω : Set Plane)
    (u : Plane → ℝ) (g : Plane → Plane)
    (h : IsPHarm p Ω u g) (hu : ContDiffOn ℝ 1 u Ω) :
    IsPHarm p Ω u (gradient u) ∧ ∀ᵐ x, x ∈ Ω → g x = gradient u x := by
  have hOopen : IsOpen Ω := h.openOmega
  have hOmeas : MeasurableSet Ω := hOopen.measurableSet
  have hp0 : (0 : ℝ) < p := by linarith
  have hudiff : ∀ x ∈ Ω, DifferentiableAt ℝ u x := fun x hx =>
    ((hu.differentiableOn one_ne_zero) x hx).differentiableAt (hOopen.mem_nhds hx)
  have hDucont : ContinuousOn (fun x => gradient u x) Ω :=
    (InnerProductSpace.toDual ℝ Plane).symm.continuous.comp_continuousOn
      (hu.continuousOn_fderiv_of_isOpen hOopen le_rfl)
  have hDfdcont : ContinuousOn (fderiv ℝ u) Ω := hu.continuousOn_fderiv_of_isOpen hOopen le_rfl
  -- `t ≤ 1 + t ^ p` for `t ≥ 0`, which is what makes `g` itself locally integrable.
  have hpow : ∀ t : ℝ, 0 ≤ t → t ≤ 1 + t ^ p := by
    intro t ht
    rcases le_or_gt t 1 with hle | hgt
    · have : (0 : ℝ) ≤ t ^ p := Real.rpow_nonneg ht p
      linarith
    · have h1 : t ^ (1 : ℝ) ≤ t ^ p := Real.rpow_le_rpow_of_exponent_le hgt.le (by linarith)
      rw [Real.rpow_one] at h1
      linarith
  obtain ⟨hval0, hgrad0⟩ := VanishingOffTsupport
  -- `g` is integrable on every compact subset of `Ω`, not merely `‖g‖ ^ p`.
  have hgint : ∀ K : Set Plane, K ⊆ Ω → IsCompact K → MeasureTheory.IntegrableOn g K := by
    intro K hK hKc
    have hgK : MeasureTheory.AEStronglyMeasurable g (MeasureTheory.volume.restrict K) :=
      h.measG.mono_measure (MeasureTheory.Measure.restrict_mono_set _ hK)
    have hb : MeasureTheory.IntegrableOn (fun x => 1 + ‖g x‖ ^ p) K :=
      (MeasureTheory.integrableOn_const hKc.measure_lt_top.ne).add (h.locIntG K hK hKc)
    refine MeasureTheory.Integrable.mono' hb hgK ?_
    filter_upwards with x using hpow _ (norm_nonneg _)
  -- Integrability of something continuous on a compact subset of `Ω` and vanishing off it.
  have hintR : ∀ (F : Plane → ℝ) (K₀ : Set Plane), IsCompact K₀ → ContinuousOn F K₀ →
      (∀ y, y ∉ K₀ → F y = 0) → MeasureTheory.Integrable F := by
    intro F K₀ hK₀c hFc hF0
    have hsupp : Function.support F ⊆ K₀ := fun y hy => by
      by_contra hc; exact hy (hF0 y hc)
    rw [← Set.indicator_eq_self.mpr hsupp,
      MeasureTheory.integrable_indicator_iff hK₀c.measurableSet]
    exact ContinuousOn.integrableOn_compact hK₀c hFc
  have hintP : ∀ (F : Plane → Plane) (K₀ : Set Plane), IsCompact K₀ → ContinuousOn F K₀ →
      (∀ y, y ∉ K₀ → F y = 0) → MeasureTheory.Integrable F := by
    intro F K₀ hK₀c hFc hF0
    have hsupp : Function.support F ⊆ K₀ := fun y hy => by
      by_contra hc; exact hy (hF0 y hc)
    rw [← Set.indicator_eq_self.mpr hsupp,
      MeasureTheory.integrable_indicator_iff hK₀c.measurableSet]
    exact ContinuousOn.integrableOn_compact hK₀c hFc
  have hlocP : ∀ K₀ : Set Plane, K₀ ⊆ Ω → ∀ F : Plane → Plane, (∀ y, y ∉ K₀ → F y = 0) →
      ∫ y in Ω, F y = ∫ y, F y := fun K₀ hK₀ F hF =>
    MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero
      fun y hy => hF y fun hc => hy (hK₀ hc)
  -- STEP 1: integration by parts.  Assembled from Mathlib's directional parts formula, which
  -- needs `u` differentiable only on `tsupport φ`, so the `C^1`-on-`Ω` hypothesis suffices.
  have hibp : ∀ φ : Plane → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ → tsupport φ ⊆ Ω →
      ∫ x in Ω, u x • gradient φ x = - ∫ x in Ω, φ x • gradient u x := by
    intro φ hφ hφc hφsub
    have hφ1 : ContDiff ℝ 1 φ := hφ.of_le (by simp)
    have hDφcont : Continuous fun y : Plane => gradient φ y :=
      ((InnerProductSpace.toDual ℝ Plane).symm.continuous).comp
        (hφ1.continuous_fderiv one_ne_zero)
    have hφdiff : ∀ x : Plane, DifferentiableAt ℝ φ x := fun x =>
      (hφ.differentiable (by simp)) x
    -- the two `Plane`-valued integrands
    have hA' : MeasureTheory.Integrable fun x => u x • gradient φ x := by
      refine hintP _ (tsupport φ) hφc ((h.contU.mono hφsub).smul hDφcont.continuousOn) ?_
      intro y hy
      rw [hgrad0 φ y hy, smul_zero]
    have hB' : MeasureTheory.Integrable fun x => φ x • gradient u x := by
      refine hintP _ (tsupport φ) hφc
        (hφ.continuous.continuousOn.smul (hDucont.mono hφsub)) ?_
      intro y hy
      rw [hval0 φ y hy, zero_smul]
    have hW : MeasureTheory.Integrable fun x => u x • gradient φ x + φ x • gradient u x :=
      hA'.add hB'
    -- the whole-space vector identity, one direction at a time
    have hWzero : ∫ x, (u x • gradient φ x + φ x • gradient u x) = 0 := by
      refine integral_eq_zero_of_forall_integral_inner_eq_zero ℝ _ hW ?_
      intro v
      have hA : MeasureTheory.Integrable fun x => u x • fderiv ℝ φ x v := by
        refine hintR _ (tsupport φ) hφc
          ((h.contU.mono hφsub).smul ((hφ1.continuous_fderiv one_ne_zero).continuousOn.clm_apply
            continuousOn_const)) ?_
        intro y hy
        show u y • fderiv ℝ φ y v = 0
        have hz : fderiv ℝ φ y v = 0 := by
          rw [← inner_gradient_left (𝕜 := ℝ), hgrad0 φ y hy, inner_zero_left]
        rw [hz, smul_zero]
      have hB : MeasureTheory.Integrable fun x => fderiv ℝ u x v • φ x := by
        refine hintR _ (tsupport φ) hφc
          (((hDfdcont.mono hφsub).clm_apply continuousOn_const).smul
            hφ.continuous.continuousOn) ?_
        intro y hy
        rw [hval0 φ y hy, smul_zero]
      have hC : MeasureTheory.Integrable fun x => u x • φ x := by
        refine hintR _ (tsupport φ) hφc
          ((h.contU.mono hφsub).smul hφ.continuous.continuousOn) ?_
        intro y hy
        rw [hval0 φ y hy, smul_zero]
      have hIBP : ∫ x, u x • fderiv ℝ φ x v = - ∫ x, fderiv ℝ u x v • φ x :=
        integral_smul_fderiv_eq_neg_fderiv_smul_of_integrable hB hA hC
          (fun x hx => hudiff x (hφsub hx)) (fun x _ => hφdiff x)
      calc ∫ x, (inner ℝ v (u x • gradient φ x + φ x • gradient u x) : ℝ)
          = ∫ x, (u x • fderiv ℝ φ x v + fderiv ℝ u x v • φ x) := by
            refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
            show (inner ℝ v (u x • gradient φ x + φ x • gradient u x) : ℝ)
              = u x • fderiv ℝ φ x v + fderiv ℝ u x v • φ x
            rw [inner_add_right, real_inner_smul_right, real_inner_smul_right,
              inner_gradient_right, inner_gradient_right]
            simp [mul_comm]
        _ = (∫ x, u x • fderiv ℝ φ x v) + ∫ x, fderiv ℝ u x v • φ x :=
            MeasureTheory.integral_add hA hB
        _ = 0 := by rw [hIBP]; ring
    have hsum : (∫ x in Ω, u x • gradient φ x) + ∫ x in Ω, φ x • gradient u x = 0 := by
      rw [← MeasureTheory.integral_add hA'.integrableOn hB'.integrableOn,
        hlocP (tsupport φ) hφsub _ (fun y hy => by
          rw [hgrad0 φ y hy, hval0 φ y hy, smul_zero, zero_smul, add_zero]), hWzero]
    rw [eq_neg_iff_add_eq_zero]
    exact hsum
  -- STEPS 2 and 3: the almost-everywhere equality, by the fundamental lemma.
  have hae : ∀ᵐ x, x ∈ Ω → g x - gradient u x = 0 := by
    refine hOopen.ae_eq_zero_of_integral_contDiff_smul_eq_zero ?_ ?_
    · refine (MeasureTheory.locallyIntegrableOn_iff hOopen.isLocallyClosed).mpr ?_
      intro K hK hKc
      exact (hgint K hK hKc).sub (ContinuousOn.integrableOn_compact hKc (hDucont.mono hK))
    · intro φ hφ hφc hφsub
      have hφg : MeasureTheory.Integrable fun x => φ x • g x := by
        have hsupp : Function.support (fun x => φ x • g x) ⊆ tsupport φ := fun y hy => by
          by_contra hc
          refine hy ?_
          show φ y • g y = 0
          rw [hval0 φ y hc, zero_smul]
        rw [← Set.indicator_eq_self.mpr hsupp,
          MeasureTheory.integrable_indicator_iff hφc.measurableSet]
        obtain ⟨B, hB⟩ := hφc.exists_bound_of_continuousOn hφ.continuous.continuousOn
        refine MeasureTheory.Integrable.mono' ((hgint _ hφsub hφc).norm.const_mul B)
          (hφ.continuous.aestronglyMeasurable.smul (hgint _ hφsub hφc).1) ?_
        filter_upwards [MeasureTheory.ae_restrict_mem hφc.measurableSet] with y hy
        rw [norm_smul]
        exact mul_le_mul_of_nonneg_right (hB y hy) (norm_nonneg _)
      have hφDu : MeasureTheory.Integrable fun x => φ x • gradient u x := by
        refine hintP _ (tsupport φ) hφc
          (hφ.continuous.continuousOn.smul (hDucont.mono hφsub)) ?_
        intro y hy
        rw [hval0 φ y hy, zero_smul]
      have hsame : ∫ x in Ω, φ x • g x = ∫ x in Ω, φ x • gradient u x := by
        have h1 := h.weakGrad φ hφ hφc hφsub
        have h2 := hibp φ hφ hφc hφsub
        rw [h1] at h2
        exact neg_inj.mp h2
      have hg1 : ∫ x in Ω, φ x • g x = ∫ x, φ x • g x :=
        hlocP (tsupport φ) hφsub _ fun y hy => by rw [hval0 φ y hy, zero_smul]
      have hg2 : ∫ x in Ω, φ x • gradient u x = ∫ x, φ x • gradient u x :=
        hlocP (tsupport φ) hφsub _ fun y hy => by rw [hval0 φ y hy, zero_smul]
      calc ∫ x, φ x • (g x - gradient u x)
          = (∫ x, φ x • g x) - ∫ x, φ x • gradient u x := by
            rw [← MeasureTheory.integral_sub hφg hφDu]
            refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
            show φ x • (g x - gradient u x) = φ x • g x - φ x • gradient u x
            rw [smul_sub]
        _ = 0 := by rw [← hg1, ← hg2, hsame, sub_self]
  have haeeq : ∀ᵐ x, x ∈ Ω → g x = gradient u x := by
    filter_upwards [hae] with x hx hxΩ
    exact sub_eq_zero.mp (hx hxΩ)
  -- STEP 4: part (a).  Four fields come from `h` unchanged; two use the classical gradient.
  refine ⟨⟨h.openOmega, h.contU, hDucont.aestronglyMeasurable hOmeas, ?_, ?_, ?_⟩, haeeq⟩
  · intro K hK hKc
    refine ContinuousOn.integrableOn_compact hKc ?_
    exact ((Real.continuous_rpow_const hp0.le).comp_continuousOn (hDucont.norm)).mono hK
  · exact fun φ hφ hφc hφsub => hibp φ hφ hφc hφsub
  · intro φ hφ hφc hφsub
    have hcong : ∫ x in Ω, (inner ℝ (PFlux p (gradient u x)) (gradient φ x) : ℝ)
        = ∫ x in Ω, (inner ℝ (PFlux p (g x)) (gradient φ x) : ℝ) := by
      refine MeasureTheory.integral_congr_ae ?_
      filter_upwards [(MeasureTheory.ae_restrict_iff' hOmeas).mpr haeeq] with x hx
      rw [hx]
    rw [hcong]
    exact h.eqn φ hφ hφc hφsub
