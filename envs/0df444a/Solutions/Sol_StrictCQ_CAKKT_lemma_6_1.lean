-- Prove2me | solution 1 for StrictCQ.CAKKT.lemma_6_1
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-04T01:01:23.616029+00:00
-- url     : https://prove2.me/submissions/162d86bb-4057-4e6f-ba3c-343f04b398a9

import Mathlib
import Definitions.Def_StrictCQ_CAKKT_Setting
import Theorems.Thm_StrictCQ_CAKKT_regNormal_eq_polar_tangentCone

open Filter Topology Set
open scoped InnerProductSpace
open StrictCQ.CAKKT

lemma cakkt_hasFDerivAt_norm {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {v : E} (hv : v ≠ 0) :
    HasFDerivAt (fun x : E => ‖x‖) (‖v‖⁻¹ • innerSL ℝ v) v := by
  have h1 := (hasStrictFDerivAt_norm_sq v).hasFDerivAt
  have hv2 : ‖v‖ ^ 2 ≠ 0 := by positivity
  have h2 := (Real.hasDerivAt_sqrt hv2).comp_hasFDerivAt v h1
  have he : (fun x : E => ‖x‖) = Real.sqrt ∘ fun x => ‖x‖ ^ 2 := by
    funext x; simp [Real.sqrt_sq (norm_nonneg x)]
  rw [he]
  refine h2.congr_fderiv ?_
  rw [Real.sqrt_sq (norm_nonneg v), ← Nat.cast_smul_eq_nsmul ℝ, smul_smul]
  congr 1
  have : ‖v‖ ≠ 0 := norm_ne_zero_iff.2 hv
  field_simp
  norm_num

/-- Radial `C¹` lemma: if `ψ` is continuous with `ψ 0 = 0`, then `v ↦ ∫₀^{‖v‖} ψ` is `C¹`,
with derivative `(ψ ‖v‖ / ‖v‖) • ⟪v, ·⟫`. -/
lemma cakkt_radial_C1 {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {ψ : ℝ → ℝ} (hψ : Continuous ψ) (hψ0 : ψ 0 = 0) :
    ContDiff ℝ 1 (fun v : E => ∫ s in (0:ℝ)..‖v‖, ψ s) ∧
    HasFDerivAt (fun v : E => ∫ s in (0:ℝ)..‖v‖, ψ s) (0 : E →L[ℝ] ℝ) (0 : E) := by
  set Φ : ℝ → ℝ := fun r => ∫ s in (0:ℝ)..r, ψ s with hΦ
  set D : E → E →L[ℝ] ℝ :=
    fun v => (ψ ‖v‖ * ‖v‖⁻¹) • innerSL ℝ (E := E) v with hD
  have hΦd : ∀ r, HasDerivAt Φ (ψ r) r := fun r => hψ.integral_hasStrictDerivAt 0 r |>.hasDerivAt
  -- derivative at 0
  have h0 : HasFDerivAt (fun v : E => Φ ‖v‖) (0 : E →L[ℝ] ℝ) (0 : E) := by
    rw [hasFDerivAt_iff_isLittleO_nhds_zero, Asymptotics.isLittleO_iff]
    intro ε hε
    have hc : ∀ᶠ s in 𝓝 (0:ℝ), ‖ψ s‖ ≤ ε := by
      have := hψ.tendsto 0
      rw [hψ0] at this
      exact this.eventually (Metric.closedBall_mem_nhds _ hε) |>.mono fun s hs => by
        simpa [dist_eq_norm] using hs
    obtain ⟨δ, hδ, hδb⟩ := Metric.eventually_nhds_iff.1 hc
    filter_upwards [Metric.ball_mem_nhds (0 : E) hδ] with h hh
    simp only [zero_add, norm_zero, zero_apply, sub_zero, hΦ,
      intervalIntegral.integral_same]
    have hhn : ‖h‖ < δ := by simpa using hh
    have := intervalIntegral.norm_integral_le_of_norm_le_const (a := 0) (b := ‖h‖) (C := ε)
      (f := ψ) (fun x hx => by
        apply hδb
        rw [Set.uIoc_of_le (norm_nonneg h)] at hx
        rw [Real.dist_eq, sub_zero, abs_of_pos hx.1]
        exact lt_of_le_of_lt hx.2 hhn)
    simpa [abs_of_nonneg (norm_nonneg h)] using this
  have hall : ∀ v, HasFDerivAt (fun v : E => Φ ‖v‖) (D v) v := by
    intro v
    rcases eq_or_ne v 0 with rfl | hv
    · simpa [hD] using h0
    · have := (hΦd ‖v‖).comp_hasFDerivAt v (cakkt_hasFDerivAt_norm hv)
      refine this.congr_fderiv ?_
      rw [hD]; simp only [smul_smul]
  have hDc : Continuous D := by
    rw [continuous_iff_continuousAt]
    intro v
    rcases eq_or_ne v 0 with rfl | hv
    · have hD0 : D 0 = 0 := by simp [hD]
      rw [ContinuousAt, hD0]
      refine squeeze_zero_norm (a := fun v => ‖ψ ‖v‖‖) (fun w => ?_) ?_
      · rw [hD]
        simp only
        rw [norm_smul, innerSL_apply_norm, Real.norm_eq_abs, abs_mul, abs_inv, abs_norm]
        rcases eq_or_ne w 0 with rfl | hw
        · simp
        · rw [mul_assoc, inv_mul_cancel₀ (norm_ne_zero_iff.2 hw), mul_one, Real.norm_eq_abs]
      · have : Tendsto (fun v : E => ψ ‖v‖) (𝓝 0) (𝓝 (ψ ‖(0 : E)‖)) :=
          (hψ.comp continuous_norm).tendsto 0
        simpa [hψ0] using this.norm
    · have hn : ‖v‖ ≠ 0 := norm_ne_zero_iff.2 hv
      have c1 : ContinuousAt (fun w : E => ψ ‖w‖ * ‖w‖⁻¹) v :=
        ((hψ.comp continuous_norm).continuousAt).mul (continuous_norm.continuousAt.inv₀ hn)
      exact c1.smul (innerSL ℝ).continuous.continuousAt
  exact ⟨contDiff_one_iff_hasFDerivAt.2 ⟨D, hDc, hall⟩, h0⟩

theorem solution {n m p : ℕ} (C : Constraints n m p) (hC : C.IsC1)
    {xbar y : EuclideanSpace ℝ (Fin n)} (hxbar : xbar ∈ C.feasible)
    (hy : y ∈ StrictCQ.AGP.polar (tangentCone C.feasible xbar)) :
    ∃ F : EuclideanSpace ℝ (Fin n) → ℝ, ContDiff ℝ 1 F ∧ -gradient F xbar = y ∧
      ∀ x ∈ C.feasible, x ≠ xbar → F xbar < F x := by
  have hyN : y ∈ regNormal C.feasible xbar := by
    rw [regNormal_eq_polar_tangentCone C.feasible hxbar]; exact hy
  set Ω := C.feasible with hΩ
  -- the modulus θ(r) = sup {⟪y, x - xbar⟫ : x ∈ Ω, ‖x - xbar‖ ≤ r}
  set A : ℝ → Set ℝ := fun r => (fun x => ⟪y, x - xbar⟫_ℝ) '' (Ω ∩ Metric.closedBall xbar r) with hA
  set θ : ℝ → ℝ := fun r => sSup (A r) with hθ
  have hAne : ∀ r, 0 ≤ r → (A r).Nonempty := fun r hr =>
    ⟨_, xbar, ⟨hxbar, Metric.mem_closedBall_self hr⟩, rfl⟩
  have hAub : ∀ r, ∀ a ∈ A r, a ≤ ‖y‖ * r := by
    rintro r a ⟨x, ⟨-, hx⟩, rfl⟩
    rw [Metric.mem_closedBall, dist_eq_norm] at hx
    calc ⟪y, x - xbar⟫_ℝ ≤ ‖y‖ * ‖x - xbar‖ := real_inner_le_norm _ _
      _ ≤ ‖y‖ * r := by gcongr
  have hAbdd : ∀ r, BddAbove (A r) := fun r => ⟨‖y‖ * r, hAub r⟩
  have hθle : ∀ x ∈ Ω, ⟪y, x - xbar⟫_ℝ ≤ θ ‖x - xbar‖ := fun x hx =>
    le_csSup (hAbdd _) ⟨x, ⟨hx, by rw [Metric.mem_closedBall, dist_eq_norm]⟩, rfl⟩
  have hθnn : ∀ r, 0 ≤ r → 0 ≤ θ r := fun r hr =>
    le_csSup_of_le (hAbdd r) ⟨xbar, ⟨hxbar, Metric.mem_closedBall_self hr⟩, rfl⟩ (by simp)
  have hθneg : ∀ r, r < 0 → θ r = 0 := by
    intro r hr
    have : A r = ∅ := by
      rw [hA, Set.image_eq_empty, Metric.closedBall_eq_empty.2 hr, Set.inter_empty]
    simp [hθ, this]
  have hθmono : Monotone θ := by
    intro r r' hrr'
    rcases lt_or_ge r 0 with hr | hr
    · rw [hθneg r hr]
      rcases lt_or_ge r' 0 with hr' | hr'
      · rw [hθneg r' hr']
      · exact hθnn r' hr'
    · refine csSup_le_csSup (hAbdd r') (hAne r hr) ?_
      rintro a ⟨x, ⟨hx, hxb⟩, rfl⟩
      exact ⟨x, ⟨hx, Metric.closedBall_subset_closedBall hrr' hxb⟩, rfl⟩
  have hθsmall : ∀ ε > (0:ℝ), ∃ δ > (0:ℝ), ∀ r, 0 ≤ r → r < δ → θ r ≤ ε * r := by
    intro ε hε
    obtain ⟨δ, hδ, hδs⟩ := Metric.mem_nhdsWithin_iff.1 (hyN.2 ε hε)
    refine ⟨δ, hδ, fun r hr hrδ => csSup_le (hAne r hr) ?_⟩
    rintro a ⟨x, ⟨hx, hxb⟩, rfl⟩
    have hxb' : x ∈ Metric.ball xbar δ := Metric.closedBall_subset_ball hrδ hxb
    have := hδs ⟨hxb', hx⟩
    rw [Metric.mem_closedBall, dist_eq_norm] at hxb
    calc ⟪y, x - xbar⟫_ℝ ≤ ε * ‖x - xbar‖ := this
      _ ≤ ε * r := by gcongr
  -- primitive Θ and the density ψ
  have hθint : ∀ a b, IntervalIntegrable θ MeasureTheory.volume a b :=
    fun a b => hθmono.intervalIntegrable
  set Θ : ℝ → ℝ := fun r => ∫ s in (0:ℝ)..r, θ s with hΘ
  have hΘc : Continuous Θ := intervalIntegral.continuous_primitive hθint 0
  have hΘdiff : ∀ a b, Θ b - Θ a = ∫ s in a..b, θ s := fun a b =>
    intervalIntegral.integral_interval_sub_left (hθint 0 b) (hθint 0 a)
  have hIbounds : ∀ s, 0 < s → 2 * s * θ (2 * s) ≤ Θ (4 * s) - Θ (2 * s) ∧
      Θ (4 * s) - Θ (2 * s) ≤ 2 * s * θ (4 * s) := by
    intro s hs
    rw [hΘdiff]
    have hle : 2 * s ≤ 4 * s := by linarith
    constructor
    · have := intervalIntegral.integral_mono_on hle (intervalIntegrable_const) (hθint _ _)
        (fun u hu => hθmono hu.1)
      simp only [intervalIntegral.integral_const, smul_eq_mul] at this
      linarith
    · have := intervalIntegral.integral_mono_on hle (hθint _ _) (intervalIntegrable_const)
        (fun u hu => hθmono hu.2)
      simp only [intervalIntegral.integral_const, smul_eq_mul] at this
      linarith
  have hIneg : ∀ s, s < 0 → Θ (4 * s) - Θ (2 * s) = 0 := by
    intro s hs
    rw [hΘdiff]
    have : ∀ u ∈ Set.uIcc (2 * s) (4 * s), θ u = 0 := by
      intro u hu
      rw [Set.uIcc_of_ge (by linarith)] at hu
      exact hθneg u (by linarith [hu.2])
    rw [intervalIntegral.integral_congr this]
    simp
  set ψ : ℝ → ℝ := fun s => (Θ (4 * s) - Θ (2 * s)) / s ^ 2 with hψ
  have hψ0 : ψ 0 = 0 := by simp [hψ]
  have hψnn : ∀ s, 0 ≤ ψ s := by
    intro s
    rcases lt_trichotomy s 0 with hs | hs | hs
    · simp [hψ, hIneg s hs]
    · simp [hψ, hs]
    · have := (hIbounds s hs).1
      have := hθnn (2 * s) (by linarith)
      exact div_nonneg (by nlinarith) (sq_nonneg _)
  have hψc : Continuous ψ := by
    rw [continuous_iff_continuousAt]
    intro s
    rcases eq_or_ne s 0 with rfl | hs
    · rw [Metric.continuousAt_iff]
      intro ε hε
      obtain ⟨δ, hδ, hδb⟩ := hθsmall (ε / 16) (by positivity)
      refine ⟨δ / 4, by positivity, fun u hu => ?_⟩
      rw [Real.dist_eq, sub_zero] at hu
      rw [hψ0, Real.dist_eq, sub_zero, abs_of_nonneg (hψnn u)]
      rcases lt_trichotomy u 0 with h | h | h
      · simp [hψ, hIneg u h]; exact hε
      · simp [hψ, h]; exact hε
      · rw [abs_of_pos h] at hu
        have h1 := (hIbounds u h).2
        have h2 := hδb (4 * u) (by linarith) (by linarith)
        have hu2 : 0 < u ^ 2 := by positivity
        rw [hψ]; simp only
        rw [div_lt_iff₀ hu2]
        nlinarith
    · have hs2 : s ^ 2 ≠ 0 := pow_ne_zero 2 hs
      exact (((hΘc.comp (continuous_const.mul continuous_id)).sub
        (hΘc.comp (continuous_const.mul continuous_id))).continuousAt).div
        (continuous_id.pow 2).continuousAt hs2
  -- Φ(r) = ∫₀ʳ ψ majorizes θ
  set Φ : ℝ → ℝ := fun r => ∫ s in (0:ℝ)..r, ψ s with hΦ
  have hΦθ : ∀ r, 0 < r → θ r ≤ Φ r := by
    intro r hr
    have hsplit : Φ r = (∫ s in (0:ℝ)..(r / 2), ψ s) + ∫ s in (r / 2)..r, ψ s :=
      (intervalIntegral.integral_add_adjacent_intervals (hψc.intervalIntegrable _ _)
        (hψc.intervalIntegrable _ _)).symm
    have h1 : 0 ≤ ∫ s in (0:ℝ)..(r / 2), ψ s :=
      intervalIntegral.integral_nonneg (by linarith) (fun s _ => hψnn s)
    have h2 : (r - r / 2) * (2 * θ r / r) ≤ ∫ s in (r / 2)..r, ψ s := by
      have := intervalIntegral.integral_mono_on (by linarith : r / 2 ≤ r)
        (intervalIntegrable_const (μ := MeasureTheory.volume) (c := 2 * θ r / r)) (hψc.intervalIntegrable _ _) ?_
      · have e : (r - r / 2) * (2 * θ r / r) = 2 * ((r - r / 2) * θ r) / r := by ring
        rw [e]; simpa [intervalIntegral.integral_const, smul_eq_mul] using this
      · intro s hs
        have hs0 : 0 < s := by linarith [hs.1]
        have hb := (hIbounds s hs0).1
        have hm : θ r ≤ θ (2 * s) := hθmono (by linarith [hs.1])
        have hθr := hθnn r hr.le
        rw [hψ]; simp only
        rw [le_div_iff₀ (by positivity)]
        have : 2 * θ r / r * s ^ 2 ≤ 2 * s * θ (2 * s) := by
          rw [div_mul_eq_mul_div, div_le_iff₀ hr]
          have := mul_le_mul_of_nonneg_left hm (by positivity : (0:ℝ) ≤ 2 * s * r)
          have h5 : θ r * s * s ≤ θ r * s * r := mul_le_mul_of_nonneg_left hs.2 (by positivity)
          nlinarith
        linarith
    have h3 : (r - r / 2) * (2 * θ r / r) = θ r := by field_simp; ring
    rw [hsplit]; linarith
  obtain ⟨hrad, hrad0⟩ := cakkt_radial_C1 (E := EuclideanSpace ℝ (Fin n)) hψc hψ0
  set F : EuclideanSpace ℝ (Fin n) → ℝ := fun x =>
    -⟪y, x - xbar⟫_ℝ + Φ ‖x - xbar‖ + ‖x - xbar‖ ^ 2 with hF
  have htr : ContDiff ℝ 1 (fun x : EuclideanSpace ℝ (Fin n) => x - xbar) :=
    contDiff_id.sub contDiff_const
  refine ⟨F, ?_, ?_, ?_⟩
  · exact ((contDiff_const.inner ℝ htr).neg.add (hrad.comp htr)).add (htr.norm_sq ℝ)
  · have hT : HasFDerivAt (fun x : EuclideanSpace ℝ (Fin n) => x - xbar)
        (ContinuousLinearMap.id ℝ _) xbar := (hasFDerivAt_id xbar).sub_const xbar
    have d1 : HasFDerivAt (fun x => -⟪y, x - xbar⟫_ℝ) (-(innerSL ℝ y)) xbar := by
      have := (innerSL ℝ y).hasFDerivAt.comp (f := fun x : EuclideanSpace ℝ (Fin n) => x - xbar) xbar hT
      exact this.neg
    have d2 : HasFDerivAt (fun x => Φ ‖x - xbar‖) (0 : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ) xbar := by
      have h0' : HasFDerivAt (fun v : EuclideanSpace ℝ (Fin n) => ∫ s in (0:ℝ)..‖v‖, ψ s)
          (0 : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ) (xbar - xbar) := by rw [sub_self]; exact hrad0
      have := h0'.comp (f := fun x : EuclideanSpace ℝ (Fin n) => x - xbar) xbar hT
      exact this
    have d3 : HasFDerivAt (fun x => ‖x - xbar‖ ^ 2) (0 : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ) xbar := by
      have := hT.norm_sq
      simpa using this
    have hd := (d1.add d2).add d3
    have hg : HasGradientAt F (-y) xbar := by
      rw [hasGradientAt_iff_hasFDerivAt]
      refine hd.congr_fderiv ?_
      ext v; simp
    rw [hg.gradient, neg_neg]
  · intro x hx hne
    have hr : 0 < ‖x - xbar‖ := norm_pos_iff.2 (sub_ne_zero.2 hne)
    have h1 := hθle x hx
    have h2 := hΦθ _ hr
    have hF0 : F xbar = 0 := by simp [hF, hΦ]
    rw [hF0]
    simp only [hF]
    have : 0 < ‖x - xbar‖ ^ 2 := by positivity
    linarith
