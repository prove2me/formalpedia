-- Prove2me | solution 1 for RegretBandits.Linear.osmd_zero_potential
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-07T07:03:37.191329+00:00
-- url     : https://prove2.me/submissions/9f9bb513-147e-4b0d-a602-c99b77d8c13a

import Mathlib
import Definitions.Def_RegretBandits_Linear_ConvexBasics
import Definitions.Def_RegretBandits_Linear_OMD
import Definitions.Def_RegretBandits_Linear_Potential
import Definitions.Def_RegretBandits_Linear_SemiBandit

open MeasureTheory

namespace OSMDsol
open Set Filter Topology RegretBandits.Linear

lemma potDom_isOpen (a : EReal) : IsOpen (potDom a) :=
  isOpen_lt continuous_coe_real_ereal continuous_const

lemma potDom_lower {a : EReal} {x y : ℝ} (hy : y ∈ potDom a) (hxy : x ≤ y) : x ∈ potDom a :=
  lt_of_le_of_lt (EReal.coe_le_coe_iff.2 hxy) hy

lemma potDom_convex (a : EReal) : Convex ℝ (potDom a) :=
  (show (potDom a).OrdConnected from ⟨fun _ _ _ hy _ hz => potDom_lower hy hz.2⟩).convex

variable {ψ : ℝ → ℝ} {a : EReal}

lemma potDom_nonempty (hψ : IsPotential 0 a ψ) : ∃ x, x ∈ potDom a := by
  obtain ⟨x, -, hx⟩ := EReal.exists_between_coe_real (bot_lt_iff_ne_bot.2 hψ.a_ne_bot)
  exact ⟨x, hx⟩

lemma ψ_cont (hψ : IsPotential 0 a ψ) : ContinuousOn ψ (potDom a) := hψ.contDiffOn.continuousOn

lemma ψ_diff (hψ : IsPotential 0 a ψ) {x : ℝ} (hx : x ∈ potDom a) : DifferentiableAt ℝ ψ x :=
  ((hψ.contDiffOn.differentiableOn one_ne_zero) x hx).differentiableAt
    ((potDom_isOpen a).mem_nhds hx)

lemma ψ_strictMono (hψ : IsPotential 0 a ψ) : StrictMonoOn ψ (potDom a) :=
  strictMonoOn_of_deriv_pos (potDom_convex a) (ψ_cont hψ)
    (fun x hx => hψ.deriv_pos x (interior_subset hx))

lemma ψ_exists_lt (hψ : IsPotential 0 a ψ) {s : ℝ} (hs : 0 < s) :
    ∃ x ∈ potDom a, ψ x < s := by
  obtain ⟨x0, hx0⟩ := potDom_nonempty hψ
  have h1 : ∀ᶠ x in atBot, ψ x < s := hψ.tendsto_atBot (Iio_mem_nhds hs)
  have h2 : ∀ᶠ x in atBot, x ≤ x0 := eventually_le_atBot x0
  obtain ⟨x, hx1, hx2⟩ := (h1.and h2).exists
  exact ⟨x, potDom_lower hx0 hx2, hx1⟩

lemma ψ_exists_gt (hψ : IsPotential 0 a ψ) (s : ℝ) : ∃ x ∈ potDom a, s < ψ x := by
  induction a using EReal.rec with
  | bot => exact absurd rfl hψ.a_ne_bot
  | coe b =>
    have h1 : ∀ᶠ x in 𝓝[<] b, s < ψ x := (hψ.tendsto_left_of_real b rfl).eventually_gt_atTop s
    have h2 : ∀ᶠ x in 𝓝[<] b, x < b := self_mem_nhdsWithin
    obtain ⟨x, hx1, hx2⟩ := (h1.and h2).exists
    exact ⟨x, EReal.coe_lt_coe_iff.2 hx2, hx1⟩
  | top =>
    obtain ⟨x, hx⟩ := ((hψ.tendsto_atTop_of_top rfl).eventually_gt_atTop s).exists
    exact ⟨x, EReal.coe_lt_top x, hx⟩

lemma ψ_surj (hψ : IsPotential 0 a ψ) {s : ℝ} (hs : 0 < s) : ∃ x ∈ potDom a, ψ x = s := by
  obtain ⟨x1, hx1, h1⟩ := ψ_exists_lt hψ hs
  obtain ⟨x2, hx2, h2⟩ := ψ_exists_gt hψ s
  have hle : x1 ≤ x2 := by
    by_contra h
    push Not at h
    have := (ψ_strictMono hψ) hx2 hx1 h
    linarith
  have hsub : Icc x1 x2 ⊆ potDom a := fun z hz => potDom_lower hx2 hz.2
  obtain ⟨z, hz, hz'⟩ := intermediate_value_Icc hle ((ψ_cont hψ).mono hsub) ⟨h1.le, h2.le⟩
  exact ⟨z, hsub hz, hz'⟩


lemma g_mem (hψ : IsPotential 0 a ψ) {s : ℝ} (hs : 0 < s) : (potInv ψ a) s ∈ potDom a :=
  Function.invFunOn_mem (ψ_surj hψ hs)

lemma ψ_g (hψ : IsPotential 0 a ψ) {s : ℝ} (hs : 0 < s) : ψ ((potInv ψ a) s) = s :=
  Function.invFunOn_eq (ψ_surj hψ hs)

lemma g_ψ (hψ : IsPotential 0 a ψ) {x : ℝ} (hx : x ∈ potDom a) : (potInv ψ a) (ψ x) = x := by
  have hpos := hψ.pos x hx
  exact (ψ_strictMono hψ).injOn (g_mem hψ hpos) hx (ψ_g hψ hpos)

lemma g_strictMono (hψ : IsPotential 0 a ψ) : StrictMonoOn (potInv ψ a) (Ioi 0) := by
  intro s hs t ht hst
  by_contra h
  push Not at h
  have := (ψ_strictMono hψ).monotoneOn (g_mem hψ ht) (g_mem hψ hs) h
  rw [ψ_g hψ hs, ψ_g hψ ht] at this
  exact absurd hst (not_lt.2 this)

lemma g_image (hψ : IsPotential 0 a ψ) : (potInv ψ a) '' Ioi 0 = potDom a := by
  ext x
  constructor
  · rintro ⟨s, hs, rfl⟩
    exact g_mem hψ hs
  · intro hx
    exact ⟨ψ x, hψ.pos x hx, g_ψ hψ hx⟩

lemma g_contAt (hψ : IsPotential 0 a ψ) {s : ℝ} (hs : 0 < s) : ContinuousAt (potInv ψ a) s := by
  apply continuousAt_of_monotoneOn_of_image_mem_nhds (g_strictMono hψ).monotoneOn
    (Ioi_mem_nhds hs)
  rw [g_image hψ]
  exact (potDom_isOpen a).mem_nhds (g_mem hψ hs)

lemma g_contOn (hψ : IsPotential 0 a ψ) : ContinuousOn (potInv ψ a) (Ioi 0) :=
  fun _ hs => (g_contAt hψ hs).continuousWithinAt

lemma g_hasDeriv (hψ : IsPotential 0 a ψ) {s : ℝ} (hs : 0 < s) :
    HasDerivAt (potInv ψ a) (deriv ψ ((potInv ψ a) s))⁻¹ s := by
  apply HasDerivAt.of_local_left_inverse (g_contAt hψ hs)
    (ψ_diff hψ (g_mem hψ hs)).hasDerivAt (hψ.deriv_pos _ (g_mem hψ hs)).ne'
  filter_upwards [Ioi_mem_nhds hs] with t ht using ψ_g hψ ht

lemma deriv_g (hψ : IsPotential 0 a ψ) {s : ℝ} (hs : 0 < s) :
    deriv (potInv ψ a) s = (deriv ψ ((potInv ψ a) s))⁻¹ := (g_hasDeriv hψ hs).deriv

lemma deriv_g_pos (hψ : IsPotential 0 a ψ) {s : ℝ} (hs : 0 < s) : 0 < deriv (potInv ψ a) s := by
  rw [deriv_g hψ hs]
  exact inv_pos.2 (hψ.deriv_pos _ (g_mem hψ hs))

/-- tangent line bound for the concave inverse: for `0 < s ≤ u`. -/
lemma g_tangent (hψ : IsPotential 0 a ψ) {s u : ℝ} (hs : 0 < s) (hsu : s ≤ u) :
    (potInv ψ a) s ≤ (potInv ψ a) u + deriv (potInv ψ a) u * (s - u) := by
  have hu : 0 < u := lt_of_lt_of_le hs hsu
  rcases hsu.lt_or_eq with hlt | heq
  · have hr : (potInv ψ a) s < (potInv ψ a) u := g_strictMono hψ hs hu hlt
    have hsl := hψ.convexOn.slope_le_deriv (g_mem hψ hs) (g_mem hψ hu) hr
      (ψ_diff hψ (g_mem hψ hu))
    rw [slope_def_field, ψ_g hψ hs, ψ_g hψ hu] at hsl
    have hd := hψ.deriv_pos _ (g_mem hψ hu)
    rw [deriv_g hψ hu]
    have hpos : 0 < (potInv ψ a) u - (potInv ψ a) s := sub_pos.2 hr
    rw [div_le_iff₀ hpos] at hsl
    have : (deriv ψ ((potInv ψ a) u))⁻¹ * (u - s) ≤ (potInv ψ a) u - (potInv ψ a) s := by
      rw [inv_mul_le_iff₀ hd]; linarith
    nlinarith
  · subst heq; simp

/-- `g → -∞` at `0+`. -/
lemma g_small (hψ : IsPotential 0 a ψ) (M : ℝ) : ∃ r, 0 < r ∧ (potInv ψ a) r < M := by
  obtain ⟨x1, hx1⟩ := potDom_nonempty hψ
  set x0 := min x1 (M - 1)
  have hx0 : x0 ∈ potDom a := potDom_lower hx1 (min_le_left _ _)
  refine ⟨ψ x0, hψ.pos x0 hx0, ?_⟩
  rw [g_ψ hψ hx0]
  have := min_le_right x1 (M - 1)
  linarith

lemma g_integrableOn01 (hψ : IsPotential 0 a ψ) : IntegrableOn (potInv ψ a) (Ioc 0 1) := by
  have hmeas : AEStronglyMeasurable (potInv ψ a) (volume.restrict (Ioc (0:ℝ) 1)) :=
    ((g_contOn hψ).mono Ioc_subset_Ioi_self).aestronglyMeasurable measurableSet_Ioc
  refine ⟨hmeas, ?_⟩
  unfold HasFiniteIntegral
  have h := hψ.integral_abs_inv_lt_top
  simp only [zero_add] at h
  simpa [Real.enorm_eq_ofReal_abs] using h

lemma g_intervalIntegrable (hψ : IsPotential 0 a ψ) {b : ℝ} (hb : 0 ≤ b) :
    IntervalIntegrable (potInv ψ a) volume 0 b := by
  have h01 : IntervalIntegrable (potInv ψ a) volume 0 1 :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).2 (g_integrableOn01 hψ)
  rcases le_total b 1 with hb1 | hb1
  · exact h01.mono_set (by
      rw [uIcc_of_le hb, uIcc_of_le zero_le_one]; exact Icc_subset_Icc le_rfl hb1)
  · have h1b : IntervalIntegrable (potInv ψ a) volume 1 b := by
      apply ContinuousOn.intervalIntegrable
      apply (g_contOn hψ).mono
      rw [uIcc_of_le hb1]
      exact fun x hx => lt_of_lt_of_le zero_lt_one hx.1
    exact h01.trans h1b

/-- the 1D primitive -/
noncomputable def G (ψ : ℝ → ℝ) (a : EReal) (u : ℝ) : ℝ := ∫ s in (0:ℝ)..u, potInv ψ a s

lemma G_zero : G ψ a 0 = 0 := by simp [G]

lemma G_hasDeriv (hψ : IsPotential 0 a ψ) {u : ℝ} (hu : 0 < u) :
    HasDerivAt (G ψ a) ((potInv ψ a) u) u :=
  intervalIntegral.integral_hasDerivAt_right (g_intervalIntegrable hψ hu.le)
    ((g_contOn hψ).stronglyMeasurableAtFilter isOpen_Ioi u hu) (g_contAt hψ hu)

lemma G_contOn (hψ : IsPotential 0 a ψ) : ContinuousOn (G ψ a) (Ici 0) := by
  intro x hx
  have hx' : (0:ℝ) ≤ x := hx
  have hx1 : (0:ℝ) ≤ x + 1 := by linarith
  have hI : IntegrableOn (potInv ψ a) (uIcc 0 (x + 1)) volume := by
    rw [uIcc_of_le hx1]
    exact (intervalIntegrable_iff_integrableOn_Icc_of_le (by linarith)).1
      (g_intervalIntegrable hψ (by linarith))
  have hc := intervalIntegral.continuousOn_primitive_interval hI
  have hmem : x ∈ uIcc 0 (x + 1) := by rw [uIcc_of_le hx1]; exact ⟨hx', by linarith⟩
  have h1 := hc x hmem
  apply h1.mono_of_mem_nhdsWithin
  rw [uIcc_of_le hx1]
  exact mem_nhdsWithin.2 ⟨Iio (x + 1), isOpen_Iio, by simp,
    fun y hy => ⟨hy.2, le_of_lt hy.1⟩⟩

lemma G_convex (hψ : IsPotential 0 a ψ) : ConvexOn ℝ (Ici 0) (G ψ a) := by
  apply MonotoneOn.convexOn_of_deriv (convex_Ici 0) (G_contOn hψ)
  · rw [interior_Ici]
    exact fun x hx => (G_hasDeriv hψ hx).differentiableAt.differentiableWithinAt
  · rw [interior_Ici]
    intro x hx y hy hxy
    rw [(G_hasDeriv hψ hx).deriv, (G_hasDeriv hψ hy).deriv]
    exact (g_strictMono hψ).monotoneOn hx hy hxy

/-- tangent inequality: `G z ≥ G w + g w (z - w)`. -/
lemma G_tangent (hψ : IsPotential 0 a ψ) {z w : ℝ} (hz : 0 ≤ z) (hw : 0 < w) :
    G ψ a w + (potInv ψ a) w * (z - w) ≤ G ψ a z := by
  have hd := (G_hasDeriv hψ hw)
  rcases lt_trichotomy z w with h | h | h
  · have := (G_convex hψ).slope_le_deriv (show z ∈ Ici 0 from hz) (show w ∈ Ici 0 from hw.le) h
      hd.differentiableAt
    rw [hd.deriv, slope_def_field, div_le_iff₀ (sub_pos.2 h)] at this
    nlinarith
  · subst h; simp
  · have := (G_convex hψ).deriv_le_slope (show w ∈ Ici 0 from hw.le) (show z ∈ Ici 0 from hz) h
      hd.differentiableAt
    rw [hd.deriv, slope_def_field, le_div_iff₀ (sub_pos.2 h)] at this
    nlinarith

lemma G_le_mul (hψ : IsPotential 0 a ψ) {r : ℝ} (hr : 0 < r) : G ψ a r ≤ r * (potInv ψ a) r := by
  have := G_tangent hψ le_rfl hr
  rw [G_zero] at this
  linarith

lemma G_le_max (hψ : IsPotential 0 a ψ) {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u ≤ 1) :
    G ψ a u ≤ max 0 (G ψ a 1) := by
  have h := (G_convex hψ).2 (Set.mem_Ici.2 le_rfl) (Set.mem_Ici.2 zero_le_one)
    (sub_nonneg.2 hu1) hu0 (by ring : (1 - u) + u = 1)
  simp only [smul_eq_mul, mul_zero, mul_one, zero_add, G_zero] at h
  calc G ψ a u ≤ u * G ψ a 1 := h
    _ ≤ max 0 (G ψ a 1) := by
      rcases le_total 0 (G ψ a 1) with h1 | h1
      · calc u * G ψ a 1 ≤ 1 * G ψ a 1 := by nlinarith
          _ ≤ _ := by simp
      · calc u * G ψ a 1 ≤ 0 := by nlinarith
          _ ≤ _ := le_max_left _ _

/-- The per-coordinate step bound. -/
lemma step_bound (hψ : IsPotential 0 a ψ) {x w Δ : ℝ} (hx : 0 < x) (hw : 0 < w) (hΔ : 0 ≤ Δ)
    (hstep : (potInv ψ a) w = (potInv ψ a) x - Δ) :
    G ψ a x - G ψ a w - (x - w) * (potInv ψ a) w ≤ Δ ^ 2 / (2 * deriv (potInv ψ a) x) := by
  set c := deriv (potInv ψ a) x with hc
  have hcpos : 0 < c := deriv_g_pos hψ hx
  have hwx : w ≤ x := by
    by_contra h
    push Not at h
    have := g_strictMono hψ hx hw h
    linarith
  have hL : c * (x - w) ≤ Δ := by
    have := g_tangent hψ hw hwx
    nlinarith
  have hint : IntervalIntegrable (potInv ψ a) volume w x := by
    apply ContinuousOn.intervalIntegrable
    apply (g_contOn hψ).mono
    rw [uIcc_of_le hwx]
    exact fun y hy => lt_of_lt_of_le hw hy.1
  have heq : G ψ a x - G ψ a w - (x - w) * (potInv ψ a) w = ∫ s in w..x, ((potInv ψ a) s - (potInv ψ a) w) := by
    rw [intervalIntegral.integral_sub hint intervalIntegrable_const,
      intervalIntegral.integral_const, smul_eq_mul, G, G,
      intervalIntegral.integral_interval_sub_left (g_intervalIntegrable hψ hx.le)
        (g_intervalIntegrable hψ hw.le)]
  have hmono : ∫ s in w..x, ((potInv ψ a) s - (potInv ψ a) w) ≤ ∫ s in w..x, (Δ + c * (s - x)) := by
    apply intervalIntegral.integral_mono_on hwx (hint.sub intervalIntegrable_const)
    · exact (continuous_const.add (continuous_const.mul
        (continuous_id.sub continuous_const))).intervalIntegrable _ _
    · intro s hs
      have := g_tangent hψ (lt_of_lt_of_le hw hs.1) hs.2
      linarith
  have hcomp : ∫ s in w..x, (Δ + c * (s - x)) = Δ * (x - w) - c * (x - w) ^ 2 / 2 := by
    have hfun : (fun s => Δ + c * (s - x)) = fun s => (Δ - c * x) + c * s := by
      funext s; ring
    rw [hfun, intervalIntegral.integral_add (f := fun _ => Δ - c * x) (g := fun s => c * s)
        intervalIntegrable_const ((continuous_const.mul continuous_id).intervalIntegrable _ _),
      intervalIntegral.integral_const_mul, integral_id, intervalIntegral.integral_const]
    simp only [smul_eq_mul]
    ring
  rw [heq]
  refine le_trans hmono ?_
  rw [hcomp, le_div_iff₀ (by positivity)]
  nlinarith [sq_nonneg (Δ - c * (x - w))]

end OSMDsol


open MeasureTheory

namespace OSMDsol
open Set Filter Topology RegretBandits.Linear

variable {ψ : ℝ → ℝ} {a : EReal} {d : ℕ}


lemma F_eq (z : Fin d → ℝ) : potentialFn ψ a 0 z = ∑ i, G ψ a (z i) := rfl

lemma hasFDeriv_F (hψ : IsPotential 0 a ψ) {z : Fin d → ℝ} (hz : z ∈ posOrthant d) :
    HasFDerivAt (potentialFn ψ a 0)
      (∑ j : Fin d, (potInv ψ a) (z j) • ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin d => ℝ) j) z := by
  have : potentialFn ψ a 0 = fun y : Fin d → ℝ => ∑ j : Fin d, (G ψ a ∘ fun y : Fin d → ℝ => y j) y := by
    funext y; rfl
  rw [this]
  apply HasFDerivAt.fun_sum
  intro j _
  exact (G_hasDeriv hψ (hz j)).comp_hasFDerivAt z (hasFDerivAt_apply j z)

lemma grad_F (hψ : IsPotential 0 a ψ) {z : Fin d → ℝ} (hz : z ∈ posOrthant d) :
    grad (potentialFn ψ a 0) z = fun i => (potInv ψ a) (z i) := by
  unfold grad
  rw [(hasFDeriv_F hψ hz).fderiv]
  funext i
  simp [Pi.single_apply]

lemma bregman_alt (F : (Fin d → ℝ) → ℝ) (y w : Fin d → ℝ) :
    bregman F y w = (F y - y ⬝ᵥ grad F w) - (F w - w ⬝ᵥ grad F w) := by
  unfold bregman; rw [sub_dotProduct]; ring

lemma breg_three (F : (Fin d → ℝ) → ℝ) (x y w : Fin d → ℝ) :
    bregman F y x - bregman F y w + bregman F x w = (grad F x - grad F w) ⬝ᵥ (x - y) := by
  simp only [bregman, sub_dotProduct, dotProduct_sub, dotProduct_comm (grad F _)]
  ring

lemma breg_pyth (F : (Fin d → ℝ) → ℝ) (y z w : Fin d → ℝ) :
    bregman F y w - bregman F y z - bregman F z w = (y - z) ⬝ᵥ (grad F z - grad F w) := by
  simp only [bregman, sub_dotProduct, dotProduct_sub]
  ring

lemma bregman_sum (hψ : IsPotential 0 a ψ) (y : Fin d → ℝ) {w : Fin d → ℝ}
    (hw : w ∈ posOrthant d) :
    bregman (potentialFn ψ a 0) y w = ∑ i, (G ψ a (y i) - G ψ a (w i) - (y i - w i) * (potInv ψ a) (w i)) := by
  rw [bregman, grad_F hψ hw, F_eq, F_eq]
  simp only [dotProduct, Pi.sub_apply, Finset.sum_sub_distrib]

lemma bregman_nonneg (hψ : IsPotential 0 a ψ) {y w : Fin d → ℝ} (hy : ∀ i, 0 ≤ y i)
    (hw : w ∈ posOrthant d) : 0 ≤ bregman (potentialFn ψ a 0) y w := by
  rw [bregman_sum hψ y hw]
  apply Finset.sum_nonneg
  intro i _
  have := G_tangent hψ (hy i) (hw i)
  linarith

lemma bregman_step (hψ : IsPotential 0 a ψ) {x w g : Fin d → ℝ} {η : ℝ} (hη : 0 < η)
    (hx : x ∈ posOrthant d) (hw : w ∈ posOrthant d) (hg : ∀ i, 0 ≤ g i)
    (hgrad : grad (potentialFn ψ a 0) w = grad (potentialFn ψ a 0) x - η • g) :
    bregman (potentialFn ψ a 0) x w ≤ η ^ 2 / 2 * ∑ i, (g i) ^ 2 / deriv (potInv ψ a) (x i) := by
  rw [bregman_sum hψ x hw, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  have hi := congrFun hgrad i
  rw [grad_F hψ hw, grad_F hψ hx] at hi
  simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at hi
  have := step_bound hψ (hx i) (hw i) (mul_nonneg hη.le (hg i)) hi
  have hc := deriv_g_pos hψ (hx i)
  calc _ ≤ (η * g i) ^ 2 / (2 * deriv (potInv ψ a) (x i)) := this
    _ = η ^ 2 / 2 * (g i ^ 2 / deriv (potInv ψ a) (x i)) := by field_simp

lemma hasDeriv_line (hψ : IsPotential 0 a ψ) {z : Fin d → ℝ} (hz : z ∈ posOrthant d)
    (y c : Fin d → ℝ) :
    HasDerivAt (fun s : ℝ => potentialFn ψ a 0 (z + s • (y - z)) - (z + s • (y - z)) ⬝ᵥ c)
      ((fun i => (potInv ψ a) (z i) - c i) ⬝ᵥ (y - z)) 0 := by
  have hline : HasDerivAt (fun s : ℝ => z + s • (y - z)) (y - z) 0 := by
    simpa using ((hasDerivAt_id (0:ℝ)).smul_const (y - z)).const_add z
  have h1 : HasDerivAt (fun s : ℝ => potentialFn ψ a 0 (z + s • (y - z)))
      ((∑ j : Fin d, (potInv ψ a) (z j) • ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin d => ℝ) j)
        (y - z)) 0 := by
    have hF' : HasFDerivAt (potentialFn ψ a 0)
        (∑ j : Fin d, (potInv ψ a) (z j) • ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin d => ℝ) j)
        (z + (0:ℝ) • (y - z)) := by
      rw [zero_smul, add_zero]; exact hasFDeriv_F hψ hz
    have h1 := hF'.comp_hasDerivAt (0:ℝ) hline
    exact h1
  have h2 : HasDerivAt (fun s : ℝ => (z + s • (y - z)) ⬝ᵥ c) ((y - z) ⬝ᵥ c) 0 := by
    have : (fun s : ℝ => (z + s • (y - z)) ⬝ᵥ c) = fun s => z ⬝ᵥ c + s * ((y - z) ⬝ᵥ c) := by
      funext s; rw [add_dotProduct, smul_dotProduct, smul_eq_mul]
    rw [this]
    simpa using ((hasDerivAt_id (0:ℝ)).mul_const ((y - z) ⬝ᵥ c)).const_add (z ⬝ᵥ c)
  refine (h1.sub h2).congr_deriv ?_
  simp only [ContinuousLinearMap.coe_sum', Finset.sum_apply, ContinuousLinearMap.coe_smul',
    Pi.smul_apply, ContinuousLinearMap.coe_proj, Function.eval, smul_eq_mul, dotProduct,
    Pi.sub_apply, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl; intro i _
  rw [ContinuousLinearMap.proj_apply, Pi.sub_apply]; ring

lemma first_order (hψ : IsPotential 0 a ψ) {K : Set (Fin d → ℝ)} (hKconv : Convex ℝ K)
    {z c : Fin d → ℝ} (hzK : z ∈ K) (hz : z ∈ posOrthant d)
    (hmin : ∀ y ∈ K, potentialFn ψ a 0 z - z ⬝ᵥ c ≤ potentialFn ψ a 0 y - y ⬝ᵥ c)
    {y : Fin d → ℝ} (hy : y ∈ K) :
    0 ≤ (grad (potentialFn ψ a 0) z - c) ⬝ᵥ (y - z) := by
  have hd := (hasDeriv_line hψ hz y c).tendsto_slope_zero_right
  have hval : (grad (potentialFn ψ a 0) z - c) = fun i => (potInv ψ a) (z i) - c i := by
    rw [grad_F hψ hz]; rfl
  rw [hval]
  apply ge_of_tendsto hd
  filter_upwards [Ioo_mem_nhdsGT (show (0:ℝ) < 1 by norm_num)] with t ht
  have hmem : z + t • (y - z) ∈ K := hKconv.add_smul_sub_mem hzK hy ⟨ht.1.le, ht.2.le⟩
  have := hmin _ hmem
  simp only [zero_add, zero_smul, add_zero, smul_eq_mul]
  apply mul_nonneg (inv_nonneg.2 ht.1.le)
  linarith

lemma interior_of_min (hψ : IsPotential 0 a ψ) {K : Set (Fin d → ℝ)} (hKconv : Convex ℝ K)
    (hK0 : ∀ y ∈ K, ∀ i, 0 ≤ y i) (hKD : (K ∩ posOrthant d).Nonempty)
    {z c : Fin d → ℝ} (hzK : z ∈ K)
    (hmin : ∀ y ∈ K, potentialFn ψ a 0 z - z ⬝ᵥ c ≤ potentialFn ψ a 0 y - y ⬝ᵥ c) :
    z ∈ posOrthant d := by
  by_contra hz
  simp only [posOrthant, mem_setOf_eq, not_forall, not_lt] at hz
  obtain ⟨i, hi⟩ := hz
  have hzi : z i = 0 := le_antisymm hi (hK0 z hzK i)
  obtain ⟨p, hpK, hpD⟩ := hKD
  have hpi : 0 < p i := hpD i
  set M := ∑ j, (G ψ a (p j) - G ψ a (z j)) - (G ψ a (p i) - G ψ a (z i)) - (p - z) ⬝ᵥ c with hM
  obtain ⟨r, hr0, hr⟩ := g_small hψ (-M / p i)
  set s := min 1 (r / p i) with hs
  have hs0 : 0 < s := lt_min one_pos (div_pos hr0 hpi)
  have hs1 : s ≤ 1 := min_le_left _ _
  have hsp : s * p i ≤ r := by
    have := min_le_right 1 (r / p i)
    rw [le_div_iff₀ hpi] at this
    linarith
  have hgs : (potInv ψ a) (s * p i) ≤ (potInv ψ a) r :=
    (g_strictMono hψ).monotoneOn (show 0 < s * p i from mul_pos hs0 hpi) hr0 hsp
  set y := z + s • (p - z) with hy
  have hyK : y ∈ K := hKconv.add_smul_sub_mem hzK hpK ⟨hs0.le, hs1⟩
  -- coordinate bounds
  have hcoord : ∀ j, G ψ a (y j) - G ψ a (z j) ≤ s * (G ψ a (p j) - G ψ a (z j)) := by
    intro j
    have h := (G_convex hψ).2 (Set.mem_Ici.2 (hK0 z hzK j)) (Set.mem_Ici.2 (hK0 p hpK j))
      (sub_nonneg.2 hs1) hs0.le (by ring : (1 - s) + s = 1)
    have hyj : y j = (1 - s) • z j + s • p j := by
      simp only [hy, Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]; ring
    rw [hyj]
    simp only [smul_eq_mul] at h ⊢
    linarith
  have hcoord_i : G ψ a (y i) - G ψ a (z i) ≤ s * (p i * (potInv ψ a) (s * p i)) := by
    have hyi : y i = s * p i := by
      simp only [hy, Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul, hzi]; ring
    rw [hyi, hzi, G_zero, sub_zero]
    have := G_le_mul hψ (mul_pos hs0 hpi)
    linarith
  have hsum : ∑ j, (G ψ a (y j) - G ψ a (z j)) ≤
      s * (∑ j, (G ψ a (p j) - G ψ a (z j)) - (G ψ a (p i) - G ψ a (z i))) +
        s * (p i * (potInv ψ a) (s * p i)) := by
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i),
      ← Finset.add_sum_erase _ (fun j => G ψ a (p j) - G ψ a (z j)) (Finset.mem_univ i)]
    have : ∑ j ∈ Finset.univ.erase i, (G ψ a (y j) - G ψ a (z j)) ≤
        ∑ j ∈ Finset.univ.erase i, s * (G ψ a (p j) - G ψ a (z j)) :=
      Finset.sum_le_sum (fun j _ => hcoord j)
    rw [← Finset.mul_sum] at this
    linarith
  have hdot : y ⬝ᵥ c = z ⬝ᵥ c + s * ((p - z) ⬝ᵥ c) := by
    rw [hy, add_dotProduct, smul_dotProduct, smul_eq_mul]
  have hFy : potentialFn ψ a 0 y - potentialFn ψ a 0 z = ∑ j, (G ψ a (y j) - G ψ a (z j)) := by
    rw [F_eq, F_eq, Finset.sum_sub_distrib]
  have hneg : M + p i * (potInv ψ a) (s * p i) < 0 := by
    have h1 : p i * (potInv ψ a) (s * p i) ≤ p i * (potInv ψ a) r := mul_le_mul_of_nonneg_left hgs hpi.le
    have h2 : p i * (potInv ψ a) r < p i * (-M / p i) := mul_lt_mul_of_pos_left hr hpi
    rw [mul_div_cancel₀ _ hpi.ne'] at h2
    linarith
  have := hmin y hyK
  have : s * (M + p i * (potInv ψ a) (s * p i)) < 0 := mul_neg_of_pos_of_neg hs0 hneg
  nlinarith

lemma run_mem (hψ : IsPotential 0 a ψ) {K : Set (Fin d → ℝ)} (hKconv : Convex ℝ K)
    (hK0 : ∀ y ∈ K, ∀ i, 0 ≤ y i) (hKD : (K ∩ posOrthant d).Nonempty) {η : ℝ}
    {g x w : ℕ → Fin d → ℝ} (hrun : IsOMDRun (potentialFn ψ a 0) (posOrthant d) K η g x w)
    {t : ℕ} (ht : 1 ≤ t) : x t ∈ posOrthant d ∧ x t ∈ K := by
  rcases Nat.exists_eq_add_of_le ht with ⟨s, rfl⟩
  rcases s with _ | s
  · refine ⟨interior_of_min hψ hKconv hK0 hKD (c := 0) hrun.1.1 ?_, hrun.1.1⟩
    intro y hy; simpa using hrun.1.2 y hy
  · have hp := (hrun.2 (s + 1) (by omega)).2.2
    rw [show 1 + (s + 1) = s + 1 + 1 by ring]
    refine ⟨interior_of_min hψ hKconv hK0 hKD (c := grad (potentialFn ψ a 0) (w (s + 1 + 1)))
      hp.1 ?_, hp.1⟩
    intro y hy
    have := hp.2 y hy
    rw [bregman_alt, bregman_alt] at this
    linarith

/-- one round of OMD -/
lemma round_bound (hψ : IsPotential 0 a ψ) {K : Set (Fin d → ℝ)} (hKconv : Convex ℝ K)
    (hK0 : ∀ y ∈ K, ∀ i, 0 ≤ y i) (hKD : (K ∩ posOrthant d).Nonempty) {η : ℝ} (hη : 0 < η)
    {g x w : ℕ → Fin d → ℝ} (hrun : IsOMDRun (potentialFn ψ a 0) (posOrthant d) K η g x w)
    (hg : ∀ t, 1 ≤ t → ∀ i, 0 ≤ g t i) {y : Fin d → ℝ} (hy : y ∈ K) {t : ℕ} (ht : 1 ≤ t) :
    η * (g t ⬝ᵥ (x t - y)) ≤ bregman (potentialFn ψ a 0) y (x t)
      - bregman (potentialFn ψ a 0) y (x (t + 1))
      + η ^ 2 / 2 * ∑ i, (g t i) ^ 2 / deriv (potInv ψ a) (x t i) := by
  obtain ⟨hwD, hgrad, hproj⟩ := hrun.2 t ht
  obtain ⟨hxD, hxK⟩ := run_mem hψ hKconv hK0 hKD hrun ht
  obtain ⟨hzD, hzK⟩ := run_mem hψ hKconv hK0 hKD hrun (show 1 ≤ t + 1 by omega)
  have h3 := breg_three (potentialFn ψ a 0) (x t) y (w (t + 1))
  have hηg : grad (potentialFn ψ a 0) (x t) - grad (potentialFn ψ a 0) (w (t + 1)) = η • g t := by
    rw [hgrad]; abel
  rw [hηg, smul_dotProduct, smul_eq_mul] at h3
  have hp := breg_pyth (potentialFn ψ a 0) y (x (t + 1)) (w (t + 1))
  have hfo : 0 ≤ (grad (potentialFn ψ a 0) (x (t + 1)) - grad (potentialFn ψ a 0) (w (t + 1)))
      ⬝ᵥ (y - x (t + 1)) := by
    apply first_order hψ hKconv hzK hzD _ hy
    intro y' hy'
    have := hproj.2 y' hy'
    rw [bregman_alt, bregman_alt] at this
    linarith
  rw [dotProduct_comm] at hfo
  have hnn := bregman_nonneg hψ (hK0 _ hzK) hwD
  have hst := bregman_step hψ hη hxD hwD (hg t ht) hgrad
  linarith

theorem pathwise (hψ : IsPotential 0 a ψ) {K : Set (Fin d → ℝ)} (hKconv : Convex ℝ K)
    (hK0 : ∀ y ∈ K, ∀ i, 0 ≤ y i) (hKD : (K ∩ posOrthant d).Nonempty) {η : ℝ} (hη : 0 < η)
    {g x w : ℕ → Fin d → ℝ} (hrun : IsOMDRun (potentialFn ψ a 0) (posOrthant d) K η g x w)
    (hg : ∀ t, 1 ≤ t → ∀ i, 0 ≤ g t i) {y : Fin d → ℝ} (hy : y ∈ K) (n : ℕ) :
    ∑ t ∈ Finset.Icc 1 n, g t ⬝ᵥ (x t - y) ≤
      (potentialFn ψ a 0 y - potentialFn ψ a 0 (x 1)) / η +
        η / 2 * ∑ t ∈ Finset.Icc 1 n, ∑ i, (g t i) ^ 2 / deriv (potInv ψ a) (x t i) := by
  have hind : ∀ n : ℕ, η * ∑ t ∈ Finset.Icc 1 n, g t ⬝ᵥ (x t - y) ≤
      bregman (potentialFn ψ a 0) y (x 1) - bregman (potentialFn ψ a 0) y (x (n + 1)) +
        η ^ 2 / 2 * ∑ t ∈ Finset.Icc 1 n, ∑ i, (g t i) ^ 2 / deriv (potInv ψ a) (x t i) := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [Finset.sum_Icc_succ_top (by omega), Finset.sum_Icc_succ_top (by omega)]
      have := round_bound hψ hKconv hK0 hKD hη hrun hg hy (show 1 ≤ n + 1 by omega)
      rw [mul_add, mul_add]
      linarith
  have h := hind n
  obtain ⟨hx1D, hx1K⟩ := run_mem hψ hKconv hK0 hKD hrun (le_refl 1)
  obtain ⟨hxnD, -⟩ := run_mem hψ hKconv hK0 hKD hrun (show 1 ≤ n + 1 by omega)
  have hnn := bregman_nonneg hψ (hK0 _ hy) hxnD
  have hfo := first_order hψ hKconv (c := 0) hx1K hx1D (by
    intro y' hy'; simpa using hrun.1.2 y' hy') hy
  have hb1 : bregman (potentialFn ψ a 0) y (x 1) ≤
      potentialFn ψ a 0 y - potentialFn ψ a 0 (x 1) := by
    rw [bregman]; rw [sub_zero, dotProduct_comm] at hfo; linarith
  set S := ∑ t ∈ Finset.Icc 1 n, g t ⬝ᵥ (x t - y)
  set T := ∑ t ∈ Finset.Icc 1 n, ∑ i, (g t i) ^ 2 / deriv (potInv ψ a) (x t i)
  have key : η * S ≤ (potentialFn ψ a 0 y - potentialFn ψ a 0 (x 1)) + η ^ 2 / 2 * T := by
    linarith
  rw [← sub_nonneg]
  have : (potentialFn ψ a 0 y - potentialFn ψ a 0 (x 1)) / η + η / 2 * T - S =
      ((potentialFn ψ a 0 y - potentialFn ψ a 0 (x 1)) + η ^ 2 / 2 * T - η * S) / η := by
    field_simp
  rw [this]
  apply div_nonneg _ hη.le
  linarith

end OSMDsol


open MeasureTheory

namespace OSMDsol
open Set Filter Topology RegretBandits.Linear

section K
variable {d m : ℕ} {C : Set (Fin d → ℝ)}

lemma K_cube (hC : IsCombinatorialSet C m) {y : Fin d → ℝ} (hy : y ∈ convexHull ℝ C) :
    ∀ i, 0 ≤ y i ∧ y i ≤ 1 := by
  have hS : Convex ℝ {z : Fin d → ℝ | ∀ i, 0 ≤ z i ∧ z i ≤ 1} := by
    intro u hu v hv s t hs ht hst i
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    have h1 := hu i; have h2 := hv i
    constructor <;> nlinarith [h1.1, h1.2, h2.1, h2.2]
  have hsub : C ⊆ {z : Fin d → ℝ | ∀ i, 0 ≤ z i ∧ z i ≤ 1} := by
    intro v hv i
    rcases (hC.2 v hv).1 i with h | h <;> rw [h] <;> norm_num
  exact convexHull_min hsub hS hy

lemma K_sum (hC : IsCombinatorialSet C m) {y : Fin d → ℝ} (hy : y ∈ convexHull ℝ C) :
    ∑ i, y i = (m : ℝ) := by
  have hS : Convex ℝ {z : Fin d → ℝ | ∑ i, z i = (m : ℝ)} := by
    intro u hu v hv s t hs ht hst
    simp only [mem_setOf_eq, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_add_distrib,
      ← Finset.mul_sum] at hu hv ⊢
    rw [hu, hv, ← add_mul, hst, one_mul]
  have hsub : C ⊆ {z : Fin d → ℝ | ∑ i, z i = (m : ℝ)} := fun v hv => (hC.2 v hv).2
  exact convexHull_min hsub hS hy

end K

section CE
variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {d : ℕ}

lemma ce_mul (X : Ω → Fin d → ℝ) (hX : Measurable X) {Y Z f : Ω → ℝ} (hY : Integrable Y P)
    (hce : condExp (MeasurableSpace.comap X inferInstance) P Y =ᵐ[P] Z)
    (hf : StronglyMeasurable[MeasurableSpace.comap X inferInstance] f) (B : ℝ)
    (hfb : ∀ ω, |f ω| ≤ B) :
    ∫ ω, f ω * Y ω ∂P = ∫ ω, f ω * Z ω ∂P := by
  have hm : MeasurableSpace.comap X inferInstance ≤ ‹MeasurableSpace Ω› := hX.comap_le
  have hfY : Integrable (f * Y) P :=
    hY.bdd_mul (hf.mono hm).aestronglyMeasurable (Eventually.of_forall fun ω => by
      simpa [Real.norm_eq_abs] using hfb ω)
  have h1 := integral_condExp (μ := P) (f := f * Y) hm
  have h2 := condExp_mul_of_stronglyMeasurable_left hf hfY hY
  rw [← show ∫ ω, (f * Y) ω ∂P = ∫ ω, f ω * Y ω ∂P from rfl, ← h1]
  apply integral_congr_ae
  filter_upwards [h2, hce] with ω h2 h3
  rw [h2, Pi.mul_apply, h3]

lemma coord_sm (X : Ω → Fin d → ℝ) (i : Fin d) :
    StronglyMeasurable[MeasurableSpace.comap X inferInstance] (fun ω => X ω i) :=
  ((measurable_pi_apply i).comp (comap_measurable X)).stronglyMeasurable

end CE

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {d m : ℕ}
  {C : Set (Fin d → ℝ)}

theorem part1 (hC : IsCombinatorialSet C m)
    (hKD : (convexHull ℝ C ∩ posOrthant d).Nonempty)
    (ℓ : ℕ → Fin d → ℝ) (n : ℕ)
    (ψ : ℝ → ℝ) (a : EReal) (hψ : IsPotential 0 a ψ)
    (η : ℝ) (hη : 0 < η) (x v ℓt w : ℕ → Ω → Fin d → ℝ) (x₁ : Fin d → ℝ)
    (hrun : ∀ ω, IsOMDRun (potentialFn ψ a 0) (posOrthant d) (convexHull ℝ C) η
        (fun t => ℓt t ω) (fun t => x t ω) (fun t => w t ω))
    (hx1 : ∀ ω, x 1 ω = x₁)
    (hxm : ∀ t, 1 ≤ t → Measurable (x t)) (hvm : ∀ t, 1 ≤ t → Measurable (v t))
    (hvC : ∀ t, 1 ≤ t → ∀ ω, v t ω ∈ C)
    (hvce : ∀ t, 1 ≤ t → condExpGiven P (x t) (v t) =ᵐ[P] x t)
    (hℓ0 : ∀ t, 1 ≤ t → ∀ ω i, 0 ≤ ℓt t ω i)
    (hℓint : ∀ t, 1 ≤ t → ∀ i, Integrable (fun ω => ℓt t ω i) P)
    (hℓce : ∀ t, 1 ≤ t → condExpGiven P (x t) (ℓt t) =ᵐ[P] fun _ => ℓ t)
    (hint2 : ∀ t, 1 ≤ t → ∀ i,
        Integrable (fun ω => ℓt t ω i ^ 2 / deriv (potInv ψ a) (x t ω i)) P)
    (y : Fin d → ℝ) (hy : y ∈ convexHull ℝ C) :
    ∫ ω, ∑ t ∈ Finset.Icc 1 n, ℓ t ⬝ᵥ v t ω ∂P - ∑ t ∈ Finset.Icc 1 n, ℓ t ⬝ᵥ y ≤
      (sSup (potentialFn ψ a 0 '' convexHull ℝ C) - potentialFn ψ a 0 x₁) / η +
        η / 2 * ∑ t ∈ Finset.Icc 1 n, ∑ i,
          ∫ ω, ℓt t ω i ^ 2 / deriv (potInv ψ a) (x t ω i) ∂P := by
  set K := convexHull ℝ C with hK
  have hKconv : Convex ℝ K := convex_convexHull ℝ C
  have hK0 : ∀ z ∈ K, ∀ i, 0 ≤ z i := fun z hz i => (K_cube hC hz i).1
  -- sSup bound
  have hbdd : BddAbove (potentialFn ψ a 0 '' K) := by
    refine ⟨(d : ℝ) * max 0 (G ψ a 1), ?_⟩
    rintro _ ⟨z, hz, rfl⟩
    rw [F_eq]
    calc ∑ i, G ψ a (z i) ≤ ∑ _i : Fin d, max 0 (G ψ a 1) :=
          Finset.sum_le_sum fun i _ => G_le_max hψ (K_cube hC hz i).1 (K_cube hC hz i).2
      _ = _ := by simp
  have hFy : potentialFn ψ a 0 y ≤ sSup (potentialFn ψ a 0 '' K) :=
    le_csSup hbdd (mem_image_of_mem _ hy)
  -- pathwise
  have hpath : ∀ ω, ∑ t ∈ Finset.Icc 1 n, ℓt t ω ⬝ᵥ (x t ω - y) ≤
      (sSup (potentialFn ψ a 0 '' K) - potentialFn ψ a 0 x₁) / η +
        η / 2 * ∑ t ∈ Finset.Icc 1 n, ∑ i, ℓt t ω i ^ 2 / deriv (potInv ψ a) (x t ω i) := by
    intro ω
    have h := pathwise hψ hKconv hK0 hKD hη (hrun ω) (fun t ht i => hℓ0 t ht ω i) hy n
    rw [hx1 ω] at h
    refine le_trans h ?_
    gcongr
  -- coordinate facts
  have hxK : ∀ t, 1 ≤ t → ∀ ω, x t ω ∈ K := fun t ht ω =>
    (run_mem hψ hKconv hK0 hKD (hrun ω) ht).2
  have hxb : ∀ t, 1 ≤ t → ∀ ω i, |x t ω i| ≤ 1 := fun t ht ω i => by
    have := K_cube hC (hxK t ht ω) i
    rw [abs_le]; constructor <;> linarith [this.1, this.2]
  have hxint : ∀ t, 1 ≤ t → ∀ i, Integrable (fun ω => x t ω i) P := fun t ht i =>
    Integrable.of_bound ((measurable_pi_apply i).comp (hxm t ht)).aestronglyMeasurable 1
      (Eventually.of_forall fun ω => by simpa [Real.norm_eq_abs] using hxb t ht ω i)
  have hvb : ∀ t, 1 ≤ t → ∀ ω i, |v t ω i| ≤ 1 := fun t ht ω i => by
    rcases (hC.2 _ (hvC t ht ω)).1 i with h | h <;> rw [h] <;> norm_num
  have hvint : ∀ t, 1 ≤ t → ∀ i, Integrable (fun ω => v t ω i) P := fun t ht i =>
    Integrable.of_bound ((measurable_pi_apply i).comp (hvm t ht)).aestronglyMeasurable 1
      (Eventually.of_forall fun ω => by simpa [Real.norm_eq_abs] using hvb t ht ω i)
  have hℓx : ∀ t, 1 ≤ t → ∀ i, Integrable (fun ω => ℓt t ω i * x t ω i) P := fun t ht i => by
    have := (hℓint t ht i).bdd_mul (c := 1)
      ((measurable_pi_apply i).comp (hxm t ht)).aestronglyMeasurable
      (Eventually.of_forall fun ω => by simpa [Real.norm_eq_abs] using hxb t ht ω i)
    simpa [mul_comm] using this
  -- E1, E2, E3
  have E1 : ∀ t, 1 ≤ t → ∀ i, ∫ ω, ℓt t ω i * x t ω i ∂P = ℓ t i * ∫ ω, x t ω i ∂P := by
    intro t ht i
    have h := ce_mul (P := P) (x t) (hxm t ht) (hℓint t ht i)
      (Z := fun _ => ℓ t i) ((hℓce t ht).mono fun ω hω => congrFun hω i)
      (coord_sm (x t) i) 1 (fun ω => hxb t ht ω i)
    calc ∫ ω, ℓt t ω i * x t ω i ∂P = ∫ ω, x t ω i * ℓt t ω i ∂P :=
          integral_congr_ae (Eventually.of_forall fun ω => mul_comm _ _)
      _ = ∫ ω, x t ω i * ℓ t i ∂P := h
      _ = _ := by
        rw [← integral_const_mul]
        exact integral_congr_ae (Eventually.of_forall fun ω => mul_comm _ _)
  have E2 : ∀ t, 1 ≤ t → ∀ i, ∫ ω, ℓt t ω i ∂P = ℓ t i := by
    intro t ht i
    have h := ce_mul (P := P) (x t) (hxm t ht) (hℓint t ht i)
      (Z := fun _ => ℓ t i) ((hℓce t ht).mono fun ω hω => congrFun hω i)
      (f := fun _ => 1) stronglyMeasurable_const 1 (fun _ => by norm_num)
    simpa using h
  have E3 : ∀ t, 1 ≤ t → ∀ i, ∫ ω, v t ω i ∂P = ∫ ω, x t ω i ∂P := by
    intro t ht i
    have h := ce_mul (P := P) (x t) (hxm t ht) (hvint t ht i)
      (Z := fun ω => x t ω i) ((hvce t ht).mono fun ω hω => congrFun hω i)
      (f := fun _ => 1) stronglyMeasurable_const 1 (fun _ => by norm_num)
    simpa using h
  -- integrability of the pathwise LHS terms
  have hLint : ∀ t ∈ Finset.Icc 1 n, Integrable (fun ω => ℓt t ω ⬝ᵥ (x t ω - y)) P := by
    intro t ht
    have ht1 : 1 ≤ t := (Finset.mem_Icc.1 ht).1
    simp only [dotProduct, Pi.sub_apply, mul_sub]
    exact integrable_finset_sum _ fun i _ => (hℓx t ht1 i).sub ((hℓint t ht1 i).mul_const _)
  have hLval : ∀ t ∈ Finset.Icc 1 n, ∫ ω, ℓt t ω ⬝ᵥ (x t ω - y) ∂P =
      ∫ ω, ℓ t ⬝ᵥ v t ω ∂P - ℓ t ⬝ᵥ y := by
    intro t ht
    have ht1 : 1 ≤ t := (Finset.mem_Icc.1 ht).1
    simp only [dotProduct, Pi.sub_apply, mul_sub]
    rw [integral_finset_sum _ fun i _ => show Integrable
        (fun ω => ℓt t ω i * x t ω i - ℓt t ω i * y i) P from
          (hℓx t ht1 i).sub ((hℓint t ht1 i).mul_const _),
      integral_finset_sum _ fun i _ => show Integrable (fun ω => ℓ t i * v t ω i) P from
        (hvint t ht1 i).const_mul _, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    rw [integral_sub (hℓx t ht1 i) ((hℓint t ht1 i).mul_const _), integral_mul_const,
      E1 t ht1 i, E2 t ht1 i, integral_const_mul, E3 t ht1 i]
  have hvint' : ∀ t ∈ Finset.Icc 1 n, Integrable (fun ω => ℓ t ⬝ᵥ v t ω) P := by
    intro t ht
    have ht1 : 1 ≤ t := (Finset.mem_Icc.1 ht).1
    simp only [dotProduct]
    exact integrable_finset_sum _ fun i _ => (hvint t ht1 i).const_mul _
  have hLHS : ∫ ω, ∑ t ∈ Finset.Icc 1 n, ℓ t ⬝ᵥ v t ω ∂P - ∑ t ∈ Finset.Icc 1 n, ℓ t ⬝ᵥ y =
      ∫ ω, ∑ t ∈ Finset.Icc 1 n, ℓt t ω ⬝ᵥ (x t ω - y) ∂P := by
    rw [integral_finset_sum _ hvint', integral_finset_sum _ hLint, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun t ht => (hLval t ht).symm
  rw [hLHS]
  have hR2 : Integrable (fun ω => ∑ t ∈ Finset.Icc 1 n, ∑ i,
      ℓt t ω i ^ 2 / deriv (potInv ψ a) (x t ω i)) P :=
    integrable_finset_sum _ fun t ht => integrable_finset_sum _ fun i _ =>
      hint2 t (Finset.mem_Icc.1 ht).1 i
  calc ∫ ω, ∑ t ∈ Finset.Icc 1 n, ℓt t ω ⬝ᵥ (x t ω - y) ∂P
      ≤ ∫ ω, ((sSup (potentialFn ψ a 0 '' K) - potentialFn ψ a 0 x₁) / η +
        η / 2 * ∑ t ∈ Finset.Icc 1 n, ∑ i, ℓt t ω i ^ 2 / deriv (potInv ψ a) (x t ω i)) ∂P :=
        integral_mono (integrable_finset_sum _ hLint)
          ((integrable_const _).add (hR2.const_mul _)) hpath
    _ = _ := by
      rw [integral_add (integrable_const _) (hR2.const_mul _), integral_const, integral_const_mul,
        integral_finset_sum _ fun t ht => integrable_finset_sum _ fun i _ =>
          hint2 t (Finset.mem_Icc.1 ht).1 i]
      have hsw : ∀ t ∈ Finset.Icc 1 n, ∫ ω, ∑ i, ℓt t ω i ^ 2 / deriv (potInv ψ a) (x t ω i) ∂P
          = ∑ i, ∫ ω, ℓt t ω i ^ 2 / deriv (potInv ψ a) (x t ω i) ∂P := fun t ht =>
        integral_finset_sum _ fun i _ => hint2 t (Finset.mem_Icc.1 ht).1 i
      rw [Finset.sum_congr rfl hsw]
      simp

end OSMDsol


open MeasureTheory

namespace OSMDsol
open Set Filter Topology RegretBandits.Linear

lemma potDom_zero : potDom 0 = Iio 0 := by
  ext x; simp [potDom, EReal.coe_neg']

lemma pow_hasDeriv {q x : ℝ} (hx : x < 0) :
    HasDerivAt (powPotential q) (q * (-x) ^ (-q - 1)) x := by
  have h1 := Real.hasDerivAt_rpow_const (x := -x) (p := -q) (Or.inl (by linarith))
  have h2 := h1.comp x (hasDerivAt_neg x)
  have : powPotential q = (fun y : ℝ => y ^ (-q)) ∘ (fun x => -x) := rfl
  rw [this]
  exact h2.congr_deriv (by ring)

lemma pow_potInv {q s : ℝ} (hq : 1 < q) (hs0 : 0 < s) :
    potInv (powPotential q) 0 s = -(s ^ (-(1 / q))) := by
  have hq0 : 0 < q := by linarith
  have hmem : -(s ^ (-(1 / q))) ∈ potDom 0 := by
    rw [potDom_zero]; simp only [mem_Iio, Left.neg_neg_iff]; exact Real.rpow_pos_of_pos hs0 _
  have hψ : powPotential q (-(s ^ (-(1 / q)))) = s := by
    unfold powPotential
    rw [neg_neg, ← Real.rpow_mul hs0.le]
    rw [show -(1 / q) * -q = 1 by field_simp]
    exact Real.rpow_one s
  have hex : ∃ r ∈ potDom 0, powPotential q r = s := ⟨_, hmem, hψ⟩
  have h1 := Function.invFunOn_eq hex
  have h2 := Function.invFunOn_mem hex
  set r := Function.invFunOn (powPotential q) (potDom 0) s with hr
  rw [potDom_zero] at h2
  have hr0 : 0 < -r := by simp at h2; linarith
  unfold potInv
  rw [← hr]
  unfold powPotential at h1
  have : (-r) = s ^ (-(1 / q)) := by
    rw [← h1, ← Real.rpow_mul hr0.le, show -q * -(1 / q) = 1 by field_simp, Real.rpow_one]
  linarith

lemma pow_isPotential {q : ℝ} (hq : 1 < q) : IsPotential 0 0 (powPotential q) := by
  have hq0 : 0 < q := by linarith
  have hderiv_eq : ∀ x ∈ Iio (0:ℝ), deriv (powPotential q) x = q * (-x) ^ (-q - 1) :=
    fun x hx => (pow_hasDeriv hx).deriv
  refine
    { nonneg := le_rfl
      a_ne_bot := by simp
      pos := ?_
      convexOn := ?_
      contDiffOn := ?_
      tendsto_atBot := ?_
      tendsto_left_of_real := ?_
      tendsto_atTop_of_top := ?_
      deriv_pos := ?_
      integral_abs_inv_lt_top := ?_ }
  · rw [potDom_zero]; intro x hx
    exact Real.rpow_pos_of_pos (by simp at hx; linarith) _
  · rw [potDom_zero]
    apply MonotoneOn.convexOn_of_deriv (convex_Iio 0)
    · intro x hx; exact (pow_hasDeriv hx).continuousAt.continuousWithinAt
    · rw [interior_Iio]; intro x hx
      exact (pow_hasDeriv hx).differentiableAt.differentiableWithinAt
    · rw [interior_Iio]
      intro x hx y hy hxy
      rw [hderiv_eq x hx, hderiv_eq y hy]
      apply mul_le_mul_of_nonneg_left _ hq0.le
      exact Real.rpow_le_rpow_of_nonpos (by simp at hy; linarith) (by linarith) (by linarith)
  · rw [potDom_zero]
    intro x hx
    have hx' : x < 0 := hx
    have : ContDiffAt ℝ 1 (powPotential q) x := by
      unfold powPotential
      exact (contDiffAt_id.neg).rpow_const_of_ne (by simp; linarith)
    exact this.contDiffWithinAt
  · have := (tendsto_rpow_neg_atTop hq0).comp tendsto_neg_atBot_atTop
    exact this
  · intro b hb
    have hb0 : b = 0 := by exact_mod_cast hb.symm
    subst hb0
    have h1 : Tendsto (fun x : ℝ => -x) (𝓝[<] 0) (𝓝[>] 0) := by
      apply tendsto_nhdsWithin_iff.2
      refine ⟨?_, ?_⟩
      · have := ((continuous_neg.tendsto (0:ℝ)).mono_left (nhdsWithin_le_nhds (s := Iio 0)))
        simpa using this
      · filter_upwards [self_mem_nhdsWithin] with x hx
        simp only [mem_Ioi, Left.neg_pos_iff]; exact hx
    exact (tendsto_rpow_neg_nhdsGT_zero (by linarith : -q < 0)).comp h1
  · intro h; exact absurd h (by simp)
  · rw [potDom_zero]; intro x hx
    rw [hderiv_eq x hx]
    exact mul_pos hq0 (Real.rpow_pos_of_pos (by simp at hx; linarith) _)
  · -- integrability of the inverse near 0
    have hI : IntegrableOn (fun s : ℝ => s ^ (-(1 / q))) (Ioc 0 1) := by
      have := intervalIntegral.intervalIntegrable_rpow' (a := 0) (b := 1)
        (show -1 < -(1 / q) by
          have : 1 / q < 1 := by rw [div_lt_one hq0]; exact hq
          linarith)
      exact (intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).1 this
    have hfin := hI.2
    unfold HasFiniteIntegral at hfin
    rw [zero_add]
    refine lt_of_eq_of_lt ?_ hfin
    apply setLIntegral_congr_fun measurableSet_Ioc
    intro s hs
    dsimp only
    rw [pow_potInv hq hs.1, Real.enorm_eq_ofReal_abs, abs_neg]

lemma deriv_pow_potInv {q s : ℝ} (hq : 1 < q) (hs : 0 < s) :
    deriv (potInv (powPotential q) 0) s = (q * (s * s ^ (1 / q)))⁻¹ := by
  rw [deriv_g (pow_isPotential hq) hs, pow_potInv hq hs]
  have hneg : -(s ^ (-(1 / q))) < 0 := by
    simp only [Left.neg_neg_iff]; exact Real.rpow_pos_of_pos hs _
  rw [(pow_hasDeriv hneg).deriv, neg_neg, ← Real.rpow_mul hs.le]
  congr 2
  rw [show -(1 / q) * (-q - 1) = 1 + 1 / q by field_simp; ring, Real.rpow_add hs, Real.rpow_one]

lemma G_pow {q u : ℝ} (hq : 1 < q) (hu : 0 ≤ u) :
    G (powPotential q) 0 u = -(q / (q - 1) * u ^ (1 - 1 / q)) := by
  have hq0 : 0 < q := by linarith
  have h1q : 1 / q < 1 := by rw [div_lt_one hq0]; exact hq
  unfold G
  have hcongr : ∫ s in (0:ℝ)..u, potInv (powPotential q) 0 s =
      ∫ s in (0:ℝ)..u, -(s ^ (-(1 / q))) := by
    apply intervalIntegral.integral_congr_ae
    filter_upwards with s hs
    rw [uIoc_of_le hu] at hs
    exact pow_potInv hq hs.1
  rw [hcongr, intervalIntegral.integral_neg, integral_rpow (Or.inl (by linarith))]
  rw [Real.zero_rpow (by linarith), show -(1 / q) + 1 = 1 - 1 / q by ring]
  have : q - 1 ≠ 0 := by linarith
  have : 1 - 1 / q ≠ 0 := by linarith
  field_simp
  ring

lemma F_pow {q : ℝ} (hq : 1 < q) {d : ℕ} {z : Fin d → ℝ} (hz : ∀ i, 0 ≤ z i) :
    potentialFn (powPotential q) 0 0 z = -(q / (q - 1) * ∑ i, z i ^ (1 - 1 / q)) := by
  rw [F_eq, Finset.mul_sum, ← Finset.sum_neg_distrib]
  exact Finset.sum_congr rfl fun i _ => G_pow hq (hz i)

lemma F_pow_nonpos {q : ℝ} (hq : 1 < q) {d : ℕ} {z : Fin d → ℝ} (hz : ∀ i, 0 ≤ z i) :
    potentialFn (powPotential q) 0 0 z ≤ 0 := by
  rw [F_pow hq hz, neg_nonpos]
  apply mul_nonneg (div_nonneg (by linarith) (by linarith))
  exact Finset.sum_nonneg fun i _ => Real.rpow_nonneg (hz i) _

lemma sum_rpow_le {d : ℕ} (z : Fin d → ℝ) (hz : ∀ i, 0 ≤ z i) {p : ℝ} (hp0 : 0 < p)
    (hp1 : p < 1) : ∑ i, z i ^ p ≤ (d : ℝ) ^ (1 - p) * (∑ i, z i) ^ p := by
  have hH := Real.holderConjugate_one_div hp0 (show 0 < 1 - p by linarith) (by ring)
  have h := Real.inner_le_Lp_mul_Lq Finset.univ (fun i => z i ^ p) (fun _ => (1:ℝ)) hH
  simp only [mul_one, abs_one, Real.one_rpow, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul] at h
  have h1 : ∀ i, |z i ^ p| ^ (1 / p) = z i := by
    intro i
    rw [abs_of_nonneg (Real.rpow_nonneg (hz i) _), ← Real.rpow_mul (hz i),
      mul_one_div_cancel hp0.ne', Real.rpow_one]
  simp only [h1, one_div_one_div] at h
  linarith

section CE2
variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {d : ℕ}

lemma ce_lintegral (X : Ω → Fin d → ℝ) (hX : Measurable X) {Y Z : Ω → ℝ}
    (hYm : Measurable Y) (hY : Integrable Y P) (hY0 : ∀ ω, 0 ≤ Y ω)
    (hZm : Measurable Z) (hZ : Integrable Z P) (hZ0 : ∀ ω, 0 ≤ Z ω)
    (hce : condExp (MeasurableSpace.comap X inferInstance) P Y =ᵐ[P] Z)
    {f : Ω → ENNReal} (hf : Measurable[MeasurableSpace.comap X inferInstance] f) :
    ∫⁻ ω, ENNReal.ofReal (Y ω) * f ω ∂P = ∫⁻ ω, ENNReal.ofReal (Z ω) * f ω ∂P := by
  have hm : MeasurableSpace.comap X inferInstance ≤ ‹MeasurableSpace Ω› := hX.comap_le
  have htrim : (P.withDensity (fun ω => ENNReal.ofReal (Y ω))).trim hm =
      (P.withDensity (fun ω => ENNReal.ofReal (Z ω))).trim hm := by
    refine @Measure.ext _ (MeasurableSpace.comap X inferInstance) _ _ (fun A hA => ?_)
    rw [trim_measurableSet_eq hm hA, trim_measurableSet_eq hm hA,
      withDensity_apply _ (hm A hA), withDensity_apply _ (hm A hA),
      ← ofReal_integral_eq_lintegral_ofReal hY.integrableOn
        (Eventually.of_forall fun ω => hY0 ω),
      ← ofReal_integral_eq_lintegral_ofReal hZ.integrableOn
        (Eventually.of_forall fun ω => hZ0 ω)]
    congr 1
    rw [← setIntegral_condExp hm hY hA]
    exact setIntegral_congr_ae (hm A hA) (hce.mono fun ω h _ => h)
  have e1 := lintegral_withDensity_eq_lintegral_mul P (ENNReal.measurable_ofReal.comp hYm)
    (hf.mono hm le_rfl)
  have e2 := lintegral_withDensity_eq_lintegral_mul P (ENNReal.measurable_ofReal.comp hZm)
    (hf.mono hm le_rfl)
  have t1 := lintegral_trim hm (μ := P.withDensity (fun ω => ENNReal.ofReal (Y ω))) hf
  have t2 := lintegral_trim hm (μ := P.withDensity (fun ω => ENNReal.ofReal (Z ω))) hf
  simp only [Pi.mul_apply, Function.comp_apply, Function.comp_def] at e1 e2
  rw [← e1, ← e2, ← t1, ← t2, htrim]

lemma ce_int (X : Ω → Fin d → ℝ) (hX : Measurable X) {Y Z φ : Ω → ℝ}
    (hYm : Measurable Y) (hY : Integrable Y P) (hY0 : ∀ ω, 0 ≤ Y ω)
    (hZm : Measurable Z) (hZ : Integrable Z P) (hZ0 : ∀ ω, 0 ≤ Z ω)
    (hce : condExp (MeasurableSpace.comap X inferInstance) P Y =ᵐ[P] Z)
    (hφ : Measurable[MeasurableSpace.comap X inferInstance] φ) (hφ0 : ∀ ω, 0 ≤ φ ω)
    (hZφ : Integrable (fun ω => Z ω * φ ω) P) :
    Integrable (fun ω => Y ω * φ ω) P ∧
      ∫ ω, Y ω * φ ω ∂P = ∫ ω, Z ω * φ ω ∂P := by
  have hm : MeasurableSpace.comap X inferInstance ≤ ‹MeasurableSpace Ω› := hX.comap_le
  have hl := ce_lintegral X hX hYm hY hY0 hZm hZ hZ0 hce (ENNReal.measurable_ofReal.comp hφ)
  simp only [Function.comp_apply] at hl
  have hY' : ∫⁻ ω, ENNReal.ofReal (Y ω * φ ω) ∂P = ∫⁻ ω, ENNReal.ofReal (Z ω * φ ω) ∂P := by
    simp only [ENNReal.ofReal_mul (hY0 _), ENNReal.ofReal_mul (hZ0 _)]
    exact hl
  have hmeasY : AEStronglyMeasurable (fun ω => Y ω * φ ω) P :=
    (hYm.mul (hφ.mono hm le_rfl)).aestronglyMeasurable
  have hYφ0 : 0 ≤ᵐ[P] fun ω => Y ω * φ ω :=
    Eventually.of_forall fun ω => mul_nonneg (hY0 ω) (hφ0 ω)
  have hZφ0 : 0 ≤ᵐ[P] fun ω => Z ω * φ ω :=
    Eventually.of_forall fun ω => mul_nonneg (hZ0 ω) (hφ0 ω)
  have hint : Integrable (fun ω => Y ω * φ ω) P := by
    refine ⟨hmeasY, ?_⟩
    rw [hasFiniteIntegral_iff_ofReal hYφ0, hY']
    exact (hasFiniteIntegral_iff_ofReal hZφ0).1 hZφ.2
  refine ⟨hint, ?_⟩
  rw [integral_eq_lintegral_of_nonneg_ae hYφ0 hmeasY,
    integral_eq_lintegral_of_nonneg_ae hZφ0 hZφ.1, hY']

end CE2

lemma final_arith {q M D N : ℝ} (hq : 1 < q) (hM : 0 < M) (hD : 0 < D) (hN : 0 < N) :
    q / (q - 1) * (D ^ (1 / q) * M ^ (1 - 1 / q)) /
        Real.sqrt (2 / (q - 1) * M ^ (1 - 2 / q) / (N * D ^ (1 - 2 / q))) +
      Real.sqrt (2 / (q - 1) * M ^ (1 - 2 / q) / (N * D ^ (1 - 2 / q))) / 2 *
        (N * (q * (D ^ (1 - 1 / q) * M ^ (1 / q)))) ≤
      q * Real.sqrt (2 / (q - 1) * M * D * N) := by
  have hq1 : 0 < q - 1 := by linarith
  have hq0 : 0 < q := by linarith
  set α := M ^ (1 - 2 / q) with hα
  set β := M ^ (1 / q) with hβ
  set γ := D ^ (1 - 2 / q) with hγ
  set δ := D ^ (1 / q) with hδ
  have hα0 : 0 < α := Real.rpow_pos_of_pos hM _
  have hβ0 : 0 < β := Real.rpow_pos_of_pos hM _
  have hγ0 : 0 < γ := Real.rpow_pos_of_pos hD _
  have hδ0 : 0 < δ := Real.rpow_pos_of_pos hD _
  have hM1 : M ^ (1 - 1 / q) = α * β := by
    rw [hα, hβ, ← Real.rpow_add hM]; ring_nf
  have hD1 : D ^ (1 - 1 / q) = γ * δ := by
    rw [hγ, hδ, ← Real.rpow_add hD]; ring_nf
  have hMe : M = α * β * β := by
    rw [hα, hβ, ← Real.rpow_add hM, ← Real.rpow_add hM]; ring_nf; simp
  have hDe : D = γ * δ * δ := by
    rw [hγ, hδ, ← Real.rpow_add hD, ← Real.rpow_add hD]; ring_nf; simp
  rw [hM1, hD1]
  set η := Real.sqrt (2 / (q - 1) * α / (N * γ)) with hη
  have hηsq : η ^ 2 = 2 / (q - 1) * α / (N * γ) := Real.sq_sqrt (by positivity)
  have hη0 : 0 < η := Real.sqrt_pos.2 (by positivity)
  -- LHS = 2 η C'
  set C' := N * (q * (γ * δ * β)) / 2 with hC'
  have hA : q / (q - 1) * (δ * (α * β)) = η ^ 2 * C' := by
    rw [hηsq, hC']; field_simp
  have hL : q / (q - 1) * (δ * (α * β)) / η + η / 2 * (N * (q * (γ * δ * β))) = 2 * η * C' := by
    rw [hA]
    have : η ^ 2 * C' / η = η * C' := by field_simp
    rw [this, hC']; ring
  rw [hL]
  have hR : q * Real.sqrt (2 / (q - 1) * M * D * N) = Real.sqrt ((2 * η * C') ^ 2) := by
    rw [Real.sqrt_sq (by positivity)]
    have h4 : (2 * η * C') ^ 2 = q ^ 2 * (2 / (q - 1) * M * D * N) := by
      have : (2 * η * C') ^ 2 = 4 * η ^ 2 * C' ^ 2 := by ring
      rw [this, hηsq, hC', hMe, hDe]; field_simp; ring
    have e : Real.sqrt (q ^ 2 * (2 / (q - 1) * M * D * N)) =
        q * Real.sqrt (2 / (q - 1) * M * D * N) := by
      rw [Real.sqrt_mul (sq_nonneg q), Real.sqrt_sq hq0.le]
    rw [← e, ← h4, Real.sqrt_sq (by positivity)]
  rw [hR, Real.sqrt_sq (by positivity)]

end OSMDsol


open MeasureTheory

namespace OSMDsol
open Set Filter Topology RegretBandits.Linear

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {d m : ℕ}
  {C : Set (Fin d → ℝ)}

theorem part2 (hC : IsCombinatorialSet C m)
    (hKD : (convexHull ℝ C ∩ posOrthant d).Nonempty)
    (ℓ : ℕ → Fin d → ℝ) (hℓ : ∀ t i, ℓ t i ∈ Set.Icc (0 : ℝ) 1) (n : ℕ)
    (q : ℝ) (hq : 1 < q) (x v w : ℕ → Ω → Fin d → ℝ)
    (hrun : ∀ ω, IsOMDRun (potentialFn (powPotential q) 0 0) (posOrthant d) (convexHull ℝ C)
        (Real.sqrt (2 / (q - 1) * (m : ℝ) ^ (1 - 2 / q) / (n * (d : ℝ) ^ (1 - 2 / q))))
        (fun t => semiBanditEstimate (ℓ t) (v t ω) (x t ω)) (fun t => x t ω)
        (fun t => w t ω))
    (hxm : ∀ t, 1 ≤ t → Measurable (x t)) (hvm : ∀ t, 1 ≤ t → Measurable (v t))
    (hvC : ∀ t, 1 ≤ t → ∀ ω, v t ω ∈ C)
    (hvce : ∀ t, 1 ≤ t → condExpGiven P (x t) (v t) =ᵐ[P] x t)
    (y : Fin d → ℝ) (hy : y ∈ convexHull ℝ C) :
    ∫ ω, ∑ t ∈ Finset.Icc 1 n, ℓ t ⬝ᵥ v t ω ∂P - ∑ t ∈ Finset.Icc 1 n, ℓ t ⬝ᵥ y ≤
      q * Real.sqrt (2 / (q - 1) * m * d * n) := by
  have hq0 : 0 < q := by linarith
  have hq1 : 0 < q - 1 := by linarith
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · simp [dotProduct]
  set K := convexHull ℝ C with hK
  have hKconv : Convex ℝ K := convex_convexHull ℝ C
  have hK0 : ∀ z ∈ K, ∀ i, 0 ≤ z i := fun z hz i => (K_cube hC hz i).1
  have hmpos : (0:ℝ) < m := by
    obtain ⟨p, hpK, hpD⟩ := hKD
    rw [← K_sum hC hpK]
    exact Finset.sum_pos (fun i _ => hpD i) ⟨⟨0, hd⟩, Finset.mem_univ _⟩
  have hdpos : (0:ℝ) < d := by exact_mod_cast hd
  have hnpos : (0:ℝ) < n := by exact_mod_cast hn
  set η := Real.sqrt (2 / (q - 1) * (m : ℝ) ^ (1 - 2 / q) / (n * (d : ℝ) ^ (1 - 2 / q)))
    with hηdef
  have hη : 0 < η := Real.sqrt_pos.2 (by
    have := Real.rpow_pos_of_pos hmpos (1 - 2 / q)
    have := Real.rpow_pos_of_pos hdpos (1 - 2 / q)
    positivity)
  have hψ := pow_isPotential hq
  have hxDK : ∀ t, 1 ≤ t → ∀ ω, x t ω ∈ posOrthant d ∧ x t ω ∈ K := fun t ht ω =>
    run_mem hψ hKconv hK0 hKD (hrun ω) ht
  have hv01 : ∀ t, 1 ≤ t → ∀ ω i, v t ω i = 0 ∨ v t ω i = 1 := fun t ht ω i =>
    (hC.2 _ (hvC t ht ω)).1 i
  have hg0 : ∀ ω t, 1 ≤ t → ∀ i, 0 ≤ semiBanditEstimate (ℓ t) (v t ω) (x t ω) i := by
    intro ω t ht i
    unfold semiBanditEstimate
    have h1 := (hℓ t i).1
    have h2 : 0 ≤ v t ω i := by rcases hv01 t ht ω i with h | h <;> rw [h] <;> norm_num
    exact div_nonneg (mul_nonneg h1 h2) ((hxDK t ht ω).1 i).le
  set A := q / (q - 1) * ((d:ℝ) ^ (1 / q) * (m:ℝ) ^ (1 - 1 / q)) with hA
  set B := (d:ℝ) ^ (1 - 1 / q) * (m:ℝ) ^ (1 / q) with hB
  have h1q : 1 / q < 1 := by rw [div_lt_one hq0]; exact hq
  have h1q0 : 0 < 1 / q := by positivity
  -- pathwise
  have hpath : ∀ ω, ∑ t ∈ Finset.Icc 1 n, ℓ t ⬝ᵥ v t ω ≤
      A / η + ∑ t ∈ Finset.Icc 1 n, ∑ i, (ℓ t i * y i * (v t ω i * (x t ω i)⁻¹) +
        η / 2 * q * (v t ω i * (x t ω i ^ (1 / q) * (x t ω i)⁻¹))) := by
    intro ω
    have h := pathwise hψ hKconv hK0 hKD hη (hrun ω) (hg0 ω) hy n
    have hL : ∑ t ∈ Finset.Icc 1 n, semiBanditEstimate (ℓ t) (v t ω) (x t ω) ⬝ᵥ (x t ω - y) =
        ∑ t ∈ Finset.Icc 1 n, ℓ t ⬝ᵥ v t ω -
          ∑ t ∈ Finset.Icc 1 n, ∑ i, ℓ t i * y i * (v t ω i * (x t ω i)⁻¹) := by
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro t ht
      have ht1 := (Finset.mem_Icc.1 ht).1
      simp only [dotProduct, semiBanditEstimate, Pi.sub_apply, ← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro i _
      have hx := ((hxDK t ht1 ω).1 i).ne'
      field_simp
    have hS : ∑ t ∈ Finset.Icc 1 n, ∑ i, semiBanditEstimate (ℓ t) (v t ω) (x t ω) i ^ 2 /
        deriv (potInv (powPotential q) 0) (x t ω i) ≤
        ∑ t ∈ Finset.Icc 1 n, ∑ i, q * (v t ω i * (x t ω i ^ (1 / q) * (x t ω i)⁻¹)) := by
      apply Finset.sum_le_sum; intro t ht
      have ht1 := (Finset.mem_Icc.1 ht).1
      apply Finset.sum_le_sum; intro i _
      have hx := (hxDK t ht1 ω).1 i
      rw [deriv_pow_potInv hq hx]
      unfold semiBanditEstimate
      have hl := hℓ t i
      have hr := Real.rpow_pos_of_pos hx (1 / q)
      rcases hv01 t ht1 ω i with hv | hv <;> rw [hv]
      · simp
      · rw [div_inv_eq_mul]
        have : (ℓ t i * 1 / x t ω i) ^ 2 * (q * (x t ω i * x t ω i ^ (1 / q))) =
            q * (ℓ t i ^ 2 * (x t ω i ^ (1 / q) * (x t ω i)⁻¹)) := by
          field_simp
        rw [this]
        apply mul_le_mul_of_nonneg_left _ hq0.le
        have h2 : ℓ t i ^ 2 ≤ 1 := by nlinarith [hl.1, hl.2]
        have h3 : 0 ≤ x t ω i ^ (1 / q) * (x t ω i)⁻¹ := by positivity
        nlinarith
    have hF : (potentialFn (powPotential q) 0 0 y - potentialFn (powPotential q) 0 0 (x 1 ω)) / η
        ≤ A / η := by
      apply div_le_div_of_nonneg_right _ hη.le
      have h1 := F_pow_nonpos hq (hK0 y hy)
      have hx1 := hxDK 1 le_rfl ω
      rw [F_pow hq (hK0 _ hx1.2)]
      have hs := sum_rpow_le (x 1 ω) (hK0 _ hx1.2) (p := 1 - 1 / q) (by linarith) (by linarith)
      rw [K_sum hC hx1.2, show 1 - (1 - 1 / q) = 1 / q by ring] at hs
      have : q / (q - 1) * ∑ i, x 1 ω i ^ (1 - 1 / q) ≤ A :=
        mul_le_mul_of_nonneg_left hs (by positivity)
      linarith
    have h4 := mul_le_mul_of_nonneg_left hS (show 0 ≤ η / 2 by positivity)
    have h5 : η / 2 * ∑ t ∈ Finset.Icc 1 n, ∑ i, q * (v t ω i * (x t ω i ^ (1 / q) * (x t ω i)⁻¹))
        = ∑ t ∈ Finset.Icc 1 n, ∑ i, η / 2 * q * (v t ω i * (x t ω i ^ (1 / q) * (x t ω i)⁻¹)) := by
      rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro t _
      rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro i _; ring
    rw [Finset.sum_congr rfl (fun t _ => Finset.sum_add_distrib), Finset.sum_add_distrib]
    linarith
  -- integration facts
  have hcm : ∀ t, ∀ i, Measurable[MeasurableSpace.comap (x t) inferInstance]
      (fun ω => x t ω i) := fun t i => (measurable_pi_apply i).comp (comap_measurable (x t))
  have hxim : ∀ t, 1 ≤ t → ∀ i, Measurable (fun ω => x t ω i) := fun t ht i =>
    (measurable_pi_apply i).comp (hxm t ht)
  have hvim : ∀ t, 1 ≤ t → ∀ i, Measurable (fun ω => v t ω i) := fun t ht i =>
    (measurable_pi_apply i).comp (hvm t ht)
  have hxb : ∀ t, 1 ≤ t → ∀ ω i, 0 ≤ x t ω i ∧ x t ω i ≤ 1 := fun t ht ω i =>
    K_cube hC (hxDK t ht ω).2 i
  have hvb : ∀ t, 1 ≤ t → ∀ ω i, 0 ≤ v t ω i ∧ v t ω i ≤ 1 := fun t ht ω i => by
    rcases hv01 t ht ω i with h | h <;> rw [h] <;> norm_num
  have hbint : ∀ (f : Ω → ℝ), Measurable f → (∀ ω, 0 ≤ f ω ∧ f ω ≤ 1) → Integrable f P :=
    fun f hf hb => Integrable.of_bound hf.aestronglyMeasurable 1
      (Eventually.of_forall fun ω => by
        rw [Real.norm_eq_abs, abs_le]; constructor <;> linarith [(hb ω).1, (hb ω).2])
  have hce : ∀ t, 1 ≤ t → ∀ i, condExp (MeasurableSpace.comap (x t) inferInstance) P
      (fun ω => v t ω i) =ᵐ[P] fun ω => x t ω i := fun t ht i =>
    (hvce t ht).mono fun ω hω => congrFun hω i
  have I1 : ∀ t, 1 ≤ t → ∀ i, Integrable (fun ω => v t ω i * (x t ω i)⁻¹) P ∧
      ∫ ω, v t ω i * (x t ω i)⁻¹ ∂P = 1 := by
    intro t ht i
    have hZφ : (fun ω => x t ω i * (x t ω i)⁻¹) = fun _ => (1:ℝ) := by
      funext ω; exact mul_inv_cancel₀ ((hxDK t ht ω).1 i).ne'
    have h := ce_int (P := P) (x t) (hxm t ht) (hvim t ht i) (hbint _ (hvim t ht i) (fun ω => hvb t ht ω i))
      (fun ω => (hvb t ht ω i).1) (hxim t ht i) (hbint _ (hxim t ht i) (fun ω => hxb t ht ω i))
      (fun ω => (hxb t ht ω i).1) (hce t ht i) (φ := fun ω => (x t ω i)⁻¹) (hcm t i).inv
      (fun ω => inv_nonneg.2 (hxb t ht ω i).1) (by rw [hZφ]; exact integrable_const _)
    refine ⟨h.1, ?_⟩
    rw [h.2, hZφ]; simp
  have I2 : ∀ t, 1 ≤ t → ∀ i, Integrable (fun ω => v t ω i * (x t ω i ^ (1 / q) * (x t ω i)⁻¹)) P ∧
      ∫ ω, v t ω i * (x t ω i ^ (1 / q) * (x t ω i)⁻¹) ∂P = ∫ ω, x t ω i ^ (1 / q) ∂P := by
    intro t ht i
    have hZφ : (fun ω => x t ω i * (x t ω i ^ (1 / q) * (x t ω i)⁻¹)) =
        fun ω => x t ω i ^ (1 / q) := by
      funext ω; field_simp [((hxDK t ht ω).1 i).ne']
    have hpm : Measurable (fun ω => x t ω i ^ (1 / q)) := (hxim t ht i).pow_const _
    have hpb : ∀ ω, 0 ≤ x t ω i ^ (1 / q) ∧ x t ω i ^ (1 / q) ≤ 1 := fun ω =>
      ⟨Real.rpow_nonneg (hxb t ht ω i).1 _,
        Real.rpow_le_one (hxb t ht ω i).1 (hxb t ht ω i).2 h1q0.le⟩
    have h := ce_int (P := P) (x t) (hxm t ht) (hvim t ht i) (hbint _ (hvim t ht i) (fun ω => hvb t ht ω i))
      (fun ω => (hvb t ht ω i).1) (hxim t ht i) (hbint _ (hxim t ht i) (fun ω => hxb t ht ω i))
      (fun ω => (hxb t ht ω i).1) (hce t ht i) (φ := fun ω => x t ω i ^ (1 / q) * (x t ω i)⁻¹)
      (((hcm t i).pow_const _).mul (hcm t i).inv)
      (fun ω => mul_nonneg (Real.rpow_nonneg (hxb t ht ω i).1 _) (inv_nonneg.2 (hxb t ht ω i).1))
      (by rw [hZφ]; exact hbint _ hpm hpb)
    refine ⟨h.1, ?_⟩
    rw [h.2, hZφ]
  -- integrate
  have hfi : ∀ t ∈ Finset.Icc 1 n, ∀ i, Integrable (fun ω => ℓ t i * y i * (v t ω i * (x t ω i)⁻¹) +
      η / 2 * q * (v t ω i * (x t ω i ^ (1 / q) * (x t ω i)⁻¹))) P := fun t ht i =>
    ((I1 t (Finset.mem_Icc.1 ht).1 i).1.const_mul _).add
      ((I2 t (Finset.mem_Icc.1 ht).1 i).1.const_mul _)
  have hRint : Integrable (fun ω => A / η + ∑ t ∈ Finset.Icc 1 n, ∑ i,
      (ℓ t i * y i * (v t ω i * (x t ω i)⁻¹) +
        η / 2 * q * (v t ω i * (x t ω i ^ (1 / q) * (x t ω i)⁻¹)))) P :=
    (integrable_const _).add (integrable_finset_sum _ fun t ht =>
      integrable_finset_sum _ fun i _ => hfi t ht i)
  have hLint : Integrable (fun ω => ∑ t ∈ Finset.Icc 1 n, ℓ t ⬝ᵥ v t ω) P := by
    apply integrable_finset_sum _ fun t ht => ?_
    simp only [dotProduct]
    exact integrable_finset_sum _ fun i _ =>
      (hbint _ (hvim t (Finset.mem_Icc.1 ht).1 i)
        (fun ω => hvb t (Finset.mem_Icc.1 ht).1 ω i)).const_mul _
  have hmono := integral_mono hLint hRint hpath
  have hRval : ∫ ω, (A / η + ∑ t ∈ Finset.Icc 1 n, ∑ i,
      (ℓ t i * y i * (v t ω i * (x t ω i)⁻¹) +
        η / 2 * q * (v t ω i * (x t ω i ^ (1 / q) * (x t ω i)⁻¹)))) ∂P =
      A / η + ∑ t ∈ Finset.Icc 1 n, ∑ i,
        (ℓ t i * y i + η / 2 * q * ∫ ω, x t ω i ^ (1 / q) ∂P) := by
    rw [integral_add (integrable_const _) (integrable_finset_sum _ fun t ht =>
      integrable_finset_sum _ fun i _ => hfi t ht i), integral_const,
      integral_finset_sum _ fun t ht => integrable_finset_sum _ fun i _ => hfi t ht i]
    simp only [probReal_univ, one_smul]
    congr 1
    apply Finset.sum_congr rfl
    intro t ht
    have ht1 := (Finset.mem_Icc.1 ht).1
    rw [integral_finset_sum _ fun i _ => hfi t ht i]
    apply Finset.sum_congr rfl
    intro i _
    rw [integral_add ((I1 t ht1 i).1.const_mul _) ((I2 t ht1 i).1.const_mul _),
      integral_const_mul, integral_const_mul, (I1 t ht1 i).2, (I2 t ht1 i).2, mul_one]
  have hBt : ∀ t ∈ Finset.Icc 1 n, ∑ i, (ℓ t i * y i + η / 2 * q * ∫ ω, x t ω i ^ (1 / q) ∂P) ≤
      ℓ t ⬝ᵥ y + η / 2 * q * B := by
    intro t ht
    have ht1 := (Finset.mem_Icc.1 ht).1
    rw [Finset.sum_add_distrib, ← Finset.mul_sum]
    have hpm : ∀ i, Integrable (fun ω => x t ω i ^ (1 / q)) P := fun i =>
      hbint _ ((hxim t ht1 i).pow_const _) (fun ω =>
        ⟨Real.rpow_nonneg (hxb t ht1 ω i).1 _,
          Real.rpow_le_one (hxb t ht1 ω i).1 (hxb t ht1 ω i).2 h1q0.le⟩)
    have hsum : ∑ i, ∫ ω, x t ω i ^ (1 / q) ∂P ≤ B := by
      rw [← integral_finset_sum _ fun i _ => hpm i]
      calc ∫ ω, ∑ i, x t ω i ^ (1 / q) ∂P ≤ ∫ _ω, B ∂P := by
            apply integral_mono (integrable_finset_sum _ fun i _ => hpm i) (integrable_const _)
            intro ω
            have hs := sum_rpow_le (x t ω) (hK0 _ (hxDK t ht1 ω).2) h1q0 h1q
            rw [K_sum hC (hxDK t ht1 ω).2] at hs
            exact hs
        _ = B := by simp
    have : η / 2 * q * ∑ i, ∫ ω, x t ω i ^ (1 / q) ∂P ≤ η / 2 * q * B :=
      mul_le_mul_of_nonneg_left hsum (by positivity)
    simp only [dotProduct]
    linarith
  have hfinal : ∫ ω, ∑ t ∈ Finset.Icc 1 n, ℓ t ⬝ᵥ v t ω ∂P - ∑ t ∈ Finset.Icc 1 n, ℓ t ⬝ᵥ y ≤
      A / η + η / 2 * (n * (q * B)) := by
    have h1 := Finset.sum_le_sum hBt
    rw [Finset.sum_add_distrib, Finset.sum_const, Nat.card_Icc, nsmul_eq_mul] at h1
    simp only [add_tsub_cancel_right] at h1
    rw [hRval] at hmono
    have : (n : ℝ) * (η / 2 * q * B) = η / 2 * (n * (q * B)) := by ring
    linarith
  refine le_trans hfinal ?_
  exact final_arith hq hmpos hdpos hnpos

end OSMDsol


open MeasureTheory
open RegretBandits.Linear

theorem solution {d m : ℕ} {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] {C : Set (Fin d → ℝ)} (hC : IsCombinatorialSet C m)
    (hKD : (convexHull ℝ C ∩ posOrthant d).Nonempty)
    (ℓ : ℕ → Fin d → ℝ) (hℓ : ∀ t i, ℓ t i ∈ Set.Icc (0 : ℝ) 1) (n : ℕ) :
    (∀ (ψ : ℝ → ℝ) (a : EReal), IsPotential 0 a ψ →
      ∀ (η : ℝ), 0 < η → ∀ (x v ℓt w : ℕ → Ω → Fin d → ℝ) (x₁ : Fin d → ℝ),
      (∀ ω, IsOMDRun (potentialFn ψ a 0) (posOrthant d) (convexHull ℝ C) η
        (fun t => ℓt t ω) (fun t => x t ω) (fun t => w t ω)) →
      (∀ ω, x 1 ω = x₁) →
      (∀ t, 1 ≤ t → Measurable (x t)) → (∀ t, 1 ≤ t → Measurable (v t)) →
      (∀ t, 1 ≤ t → ∀ ω, v t ω ∈ C) →
      (∀ t, 1 ≤ t → condExpGiven P (x t) (v t) =ᵐ[P] x t) →
      (∀ t, 1 ≤ t → ∀ ω i, 0 ≤ ℓt t ω i) →
      (∀ t, 1 ≤ t → ∀ i, Integrable (fun ω => ℓt t ω i) P) →
      (∀ t, 1 ≤ t → condExpGiven P (x t) (ℓt t) =ᵐ[P] fun _ => ℓ t) →
      (∀ t, 1 ≤ t → ∀ i,
        Integrable (fun ω => ℓt t ω i ^ 2 / deriv (potInv ψ a) (x t ω i)) P) →
      ∀ y ∈ convexHull ℝ C,
        ∫ ω, ∑ t ∈ Finset.Icc 1 n, ℓ t ⬝ᵥ v t ω ∂P - ∑ t ∈ Finset.Icc 1 n, ℓ t ⬝ᵥ y ≤
          (sSup (potentialFn ψ a 0 '' convexHull ℝ C) - potentialFn ψ a 0 x₁) / η +
            η / 2 * ∑ t ∈ Finset.Icc 1 n, ∑ i,
              ∫ ω, ℓt t ω i ^ 2 / deriv (potInv ψ a) (x t ω i) ∂P) ∧
    (∀ (q : ℝ), 1 < q → ∀ (x v w : ℕ → Ω → Fin d → ℝ),
      (∀ ω, IsOMDRun (potentialFn (powPotential q) 0 0) (posOrthant d) (convexHull ℝ C)
        (Real.sqrt (2 / (q - 1) * (m : ℝ) ^ (1 - 2 / q) / (n * (d : ℝ) ^ (1 - 2 / q))))
        (fun t => semiBanditEstimate (ℓ t) (v t ω) (x t ω)) (fun t => x t ω)
        (fun t => w t ω)) →
      (∀ t, 1 ≤ t → Measurable (x t)) → (∀ t, 1 ≤ t → Measurable (v t)) →
      (∀ t, 1 ≤ t → ∀ ω, v t ω ∈ C) →
      (∀ t, 1 ≤ t → condExpGiven P (x t) (v t) =ᵐ[P] x t) →
      ∀ y ∈ convexHull ℝ C,
        ∫ ω, ∑ t ∈ Finset.Icc 1 n, ℓ t ⬝ᵥ v t ω ∂P - ∑ t ∈ Finset.Icc 1 n, ℓ t ⬝ᵥ y ≤
          q * Real.sqrt (2 / (q - 1) * m * d * n)) ∧
    (∀ (x v w : ℕ → Ω → Fin d → ℝ),
      (∀ ω, IsOMDRun (potentialFn (powPotential 2) 0 0) (posOrthant d) (convexHull ℝ C)
        (Real.sqrt (2 / n))
        (fun t => semiBanditEstimate (ℓ t) (v t ω) (x t ω)) (fun t => x t ω)
        (fun t => w t ω)) →
      (∀ t, 1 ≤ t → Measurable (x t)) → (∀ t, 1 ≤ t → Measurable (v t)) →
      (∀ t, 1 ≤ t → ∀ ω, v t ω ∈ C) →
      (∀ t, 1 ≤ t → condExpGiven P (x t) (v t) =ᵐ[P] x t) →
      ∀ y ∈ convexHull ℝ C,
        ∫ ω, ∑ t ∈ Finset.Icc 1 n, ℓ t ⬝ᵥ v t ω ∂P - ∑ t ∈ Finset.Icc 1 n, ℓ t ⬝ᵥ y ≤
          2 * Real.sqrt (2 * m * d * n)) := by
  refine ⟨?_, ?_, ?_⟩
  · intro ψ a hψ η hη x v ℓt w x₁ hrun hx1 hxm hvm hvC hvce hℓ0 hℓint hℓce hint2 y hy
    exact OSMDsol.part1 (P := P) hC hKD ℓ n ψ a hψ η hη x v ℓt w x₁ hrun hx1 hxm hvm hvC hvce
      hℓ0 hℓint hℓce hint2 y hy
  · intro q hq x v w hrun hxm hvm hvC hvce y hy
    exact OSMDsol.part2 (P := P) hC hKD ℓ hℓ n q hq x v w hrun hxm hvm hvC hvce y hy
  · intro x v w hrun hxm hvm hvC hvce y hy
    have h := OSMDsol.part2 (P := P) hC hKD ℓ hℓ n 2 (by norm_num) x v w (by
      intro ω
      convert hrun ω using 3
      all_goals simp only [show (1:ℝ) - 2 / 2 = 0 by norm_num, Real.rpow_zero]
      all_goals norm_num) hxm hvm hvC hvce y hy
    convert h using 2
    norm_num
