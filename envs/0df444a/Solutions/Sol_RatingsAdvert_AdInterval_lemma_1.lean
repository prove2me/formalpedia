-- Prove2me | solution 1 for RatingsAdvert.AdInterval.lemma_1
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-01T08:14:50.302268+00:00
-- url     : https://prove2.me/submissions/feca4ad7-cc80-44b0-bc32-6aa48f64a007

import Mathlib
import Definitions.Def_RatingsAdvert_AdInterval_Model

namespace RatingsAdvert.AdInterval
namespace RAH

open Set

/-- optimized second-period profit -/
noncomputable def g (P : Params) (x : ℝ) : ℝ := ((1 + P.beta * x - P.tau) / 2) ^ 2

lemma qe_mem (P : Params) (q z ze : ℝ) : qe P q z ze ∈ Icc (0 : ℝ) 2 :=
  ⟨le_min (le_max_left _ _) (by norm_num), min_le_right _ _⟩

/-- a maximizer of `p (2m - p)` is `m` -/
lemma argmax_quad (m p : ℝ) (h : m * (2 * m - m) ≤ p * (2 * m - p)) : p = m := by
  have h1 : (p - m) ^ 2 ≤ 0 := by nlinarith
  have h2 : (p - m) ^ 2 = 0 := le_antisymm h1 (sq_nonneg _)
  have := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp h2
  linarith

lemma p2_eq (P : Params) (x p : ℝ) (h : ∀ p', p' * D2Info P x p' ≤ p * D2Info P x p) :
    p = (1 + P.beta * x - P.tau) / 2 := by
  apply argmax_quad
  have := h ((1 + P.beta * x - P.tau) / 2)
  unfold D2Info at this
  linarith [this]

lemma p2_bench_eq (P : Params) (p : ℝ) (h : ∀ p', p' * D2Bench P p' ≤ p * D2Bench P p) :
    p = (1 + P.beta - P.tau) / 2 := by
  apply argmax_quad
  have := h ((1 + P.beta - P.tau) / 2)
  unfold D2Bench at this
  linarith [this]

lemma p2_profit (P : Params) (x p : ℝ) (hp : p = (1 + P.beta * x - P.tau) / 2) :
    p * D2Info P x p = g P x := by
  subst hp; unfold D2Info g; ring

lemma D1_le (P : Params) (z ze p : ℝ) (hz : 0 ≤ z) :
    p * D1 P z ze p ≤ z * ((1 + P.beta - ze * P.tau) / 2) ^ 2 := by
  unfold D1
  nlinarith [mul_nonneg hz (sq_nonneg (p - (1 + P.beta - ze * P.tau) / 2))]

lemma D1_opt (P : Params) (z ze : ℝ) :
    (1 + P.beta - ze * P.tau) / 2 * D1 P z ze ((1 + P.beta - ze * P.tau) / 2) =
      z * ((1 + P.beta - ze * P.tau) / 2) ^ 2 := by
  unfold D1; ring

lemma p1_eq (P : Params) (z p1 : ℝ) (hz : 0 < z)
    (h : ∀ p', p' * D1 P z z p' ≤ p1 * D1 P z z p1) : p1 = (1 + P.beta - z * P.tau) / 2 := by
  apply argmax_quad
  have := h ((1 + P.beta - z * P.tau) / 2)
  unfold D1 at this
  have h' : z * ((1 + P.beta - z * P.tau) / 2 * (2 * ((1 + P.beta - z * P.tau) / 2) -
      (1 + P.beta - z * P.tau) / 2)) ≤ z * (p1 * (2 * ((1 + P.beta - z * P.tau) / 2) - p1)) := by
    nlinarith [this]
  exact le_of_mul_le_mul_left h' hz

/-! ## Facts about `A` -/

lemma A_diff (P : Params) (hS : P.Standing) : Differentiable ℝ P.A := by
  obtain ⟨-, -, -, -, hA, -⟩ := hS
  exact hA.differentiable (by norm_num)

lemma A'_diff (P : Params) (hS : P.Standing) : Differentiable ℝ (deriv P.A) := by
  obtain ⟨-, -, -, -, hA, -⟩ := hS
  have : ContDiff ℝ 1 (deriv P.A) := hA.iterate_deriv' 1 1
  exact this.differentiable (by norm_num)

/-- `A' t - (τ/β) t` is monotone on `[0,1]`. -/
lemma A'_mono (P : Params) (hS : P.Standing) :
    MonotoneOn (fun t => deriv P.A t - P.tau / P.beta * t) (Icc (0 : ℝ) 1) := by
  have hd := A'_diff P hS
  obtain ⟨-, -, -, -, -, -, -, h2, -⟩ := hS
  apply monotoneOn_of_deriv_nonneg (convex_Icc 0 1)
  · exact ((hd.sub (differentiable_id.const_mul _))).continuous.continuousOn
  · exact ((hd.sub (differentiable_id.const_mul _))).differentiableOn
  · intro t ht
    rw [interior_Icc] at ht
    have : deriv (fun t => deriv P.A t - P.tau / P.beta * t) t =
        deriv (deriv P.A) t - P.tau / P.beta := by
      have h1 : HasDerivAt (fun t => deriv P.A t - P.tau / P.beta * t)
          (deriv (deriv P.A) t - P.tau / P.beta * 1) t :=
        (hd t).hasDerivAt.sub ((hasDerivAt_id t).const_mul _)
      rw [h1.deriv]; ring
    rw [this]
    linarith [h2 t (Ioo_subset_Icc_self ht)]

/-- the strong convexity bound for `A` on `[0,1]`. -/
lemma A_convex (P : Params) (hS : P.Standing) (z z' : ℝ) (hz : z ∈ Icc (0 : ℝ) 1)
    (hz' : z' ∈ Icc (0 : ℝ) 1) :
    deriv P.A z * (z' - z) + P.tau / P.beta * (z' - z) ^ 2 / 2 ≤ P.A z' - P.A z := by
  have hA := A_diff P hS
  have hm := A'_mono P hS
  set k := P.tau / P.beta
  -- u t = A t - A'(z) t - k (t - z)^2/2
  set u : ℝ → ℝ := fun t => P.A t - deriv P.A z * t - k * (t - z) ^ 2 / 2 with hu
  have hud : ∀ t, HasDerivAt u (deriv P.A t - deriv P.A z - k * (t - z)) t := by
    intro t
    have h3 : HasDerivAt (fun t => P.A t - deriv P.A z * t - k * (t - z) ^ 2 / 2)
        (deriv P.A t - deriv P.A z * 1 - k * (2 * (t - z) ^ 1 * 1) / 2) t := by
      have := (((hasDerivAt_id' t).sub_const z).pow 2).const_mul k |>.div_const 2
      exact ((hA t).hasDerivAt.sub ((hasDerivAt_id' t).const_mul _)).sub (by simpa using this)
    convert h3 using 1
    ring
  have hcont : Continuous u := by
    have : Differentiable ℝ u := fun t => (hud t).differentiableAt
    exact this.continuous
  rcases le_total z z' with hzz | hzz
  · -- u monotone on [z, 1]
    have : MonotoneOn u (Icc z 1) := by
      apply monotoneOn_of_deriv_nonneg (convex_Icc z 1) hcont.continuousOn
        (fun t _ => (hud t).differentiableAt.differentiableWithinAt)
      intro t ht
      rw [interior_Icc] at ht
      rw [(hud t).deriv]
      have := hm hz ⟨by linarith [hz.1, ht.1], ht.2.le⟩ ht.1.le
      simp only at this
      nlinarith
    have := this ⟨le_refl z, hz.2⟩ ⟨hzz, hz'.2⟩ hzz
    simp only [hu] at this
    nlinarith
  · have : AntitoneOn u (Icc 0 z) := by
      apply antitoneOn_of_deriv_nonpos (convex_Icc 0 z) hcont.continuousOn
        (fun t _ => (hud t).differentiableAt.differentiableWithinAt)
      intro t ht
      rw [interior_Icc] at ht
      rw [(hud t).deriv]
      have := hm ⟨ht.1.le, by linarith [hz.2, ht.2]⟩ hz ht.2.le
      simp only at this
      nlinarith
    have := this ⟨hz'.1, hzz⟩ ⟨hz.1, le_refl z⟩ hzz
    simp only [hu] at this
    nlinarith

/-- `A'` is strictly monotone on `[0,1]`. -/
lemma A'_strict (P : Params) (hS : P.Standing) (x y : ℝ) (hx : x ∈ Icc (0 : ℝ) 1)
    (hy : y ∈ Icc (0 : ℝ) 1) (hxy : x < y) : deriv P.A x < deriv P.A y := by
  have h1 := A_convex P hS x y hx hy
  have h2 := A_convex P hS y x hy hx
  have hk : 0 < P.tau / P.beta := div_pos hS.1 hS.2.2.1
  have : 0 < (y - x) := by linarith
  nlinarith [mul_pos hk (mul_pos this this)]

/-! ## one-sided Fermat -/

lemma deriv_nonpos_of_max_right (F : ℝ → ℝ) (φ a b : ℝ) (hab : a < b) (hF : HasDerivAt F φ a)
    (hmax : ∀ x ∈ Icc a b, F x ≤ F a) : φ ≤ 0 := by
  have hmo : IsMaxOn F (Icc a b) a := fun x hx => hmax x hx
  have hloc : IsLocalMaxOn F (Icc a b) a := hmo.localize
  have hy : b - a ∈ posTangentConeAt (Icc a b) a :=
    sub_mem_posTangentConeAt_of_segment_subset (segment_eq_Icc hab.le ▸ Subset.rfl)
  have := hloc.hasFDerivWithinAt_nonpos hF.hasDerivWithinAt hy
  simp at this
  nlinarith [sub_pos.mpr hab]

lemma deriv_nonneg_of_max_left (F : ℝ → ℝ) (φ a b : ℝ) (hab : a < b) (hF : HasDerivAt F φ b)
    (hmax : ∀ x ∈ Icc a b, F x ≤ F b) : 0 ≤ φ := by
  have hmo : IsMaxOn F (Icc a b) b := fun x hx => hmax x hx
  have hloc : IsLocalMaxOn F (Icc a b) b := hmo.localize
  have hy : a - b ∈ posTangentConeAt (Icc a b) b :=
    sub_mem_posTangentConeAt_of_segment_subset (by rw [segment_symm, segment_eq_Icc hab.le])
  have := hloc.hasFDerivWithinAt_nonpos hF.hasDerivWithinAt hy
  simp at this
  nlinarith [sub_pos.mpr hab]

end RAH
end RatingsAdvert.AdInterval


namespace RatingsAdvert.AdInterval
namespace RAH

open Set

lemma int_lin (d : ℝ) : ∫ q in (0:ℝ)..d, (d - q) = d ^ 2 / 2 := by
  rw [intervalIntegral.integral_sub intervalIntegrable_const intervalIntegral.intervalIntegrable_id]
  rw [intervalIntegral.integral_const, integral_id]
  simp
  ring

lemma int_lin2 (d : ℝ) : ∫ q in (0:ℝ)..2, (d - q) = 2 * d - 2 := by
  rw [intervalIntegral.integral_sub intervalIntegrable_const intervalIntegral.intervalIntegrable_id]
  rw [intervalIntegral.integral_const, integral_id]
  simp
  ring

lemma int_max (d : ℝ) : ∫ q in (0:ℝ)..2, max 0 (d - q) ≤ d ^ 2 / 2 := by
  have hc : Continuous fun q : ℝ => max 0 (d - q) := by fun_prop
  rcases le_total d 0 with hd | hd
  · have : ∫ q in (0:ℝ)..2, max 0 (d - q) = ∫ q in (0:ℝ)..2, (0:ℝ) := by
      apply intervalIntegral.integral_congr
      intro q hq
      rw [uIcc_of_le (by norm_num)] at hq
      simp only
      rw [max_eq_left (by linarith [hq.1])]
    rw [this]; simp; positivity
  rcases le_total d 2 with hd2 | hd2
  · rw [← intervalIntegral.integral_add_adjacent_intervals (b := d)
      (hc.intervalIntegrable _ _) (hc.intervalIntegrable _ _)]
    have e1 : ∫ q in (0:ℝ)..d, max 0 (d - q) = ∫ q in (0:ℝ)..d, (d - q) := by
      apply intervalIntegral.integral_congr
      intro q hq
      rw [uIcc_of_le hd] at hq
      simp only
      rw [max_eq_right (by linarith [hq.2])]
    have e2 : ∫ q in d..2, max 0 (d - q) = ∫ q in d..2, (0:ℝ) := by
      apply intervalIntegral.integral_congr
      intro q hq
      rw [uIcc_of_le hd2] at hq
      simp only
      rw [max_eq_left (by linarith [hq.1])]
    rw [e1, e2, int_lin]; simp
  · have : ∫ q in (0:ℝ)..2, max 0 (d - q) = ∫ q in (0:ℝ)..2, (d - q) := by
      apply intervalIntegral.integral_congr
      intro q hq
      rw [uIcc_of_le (by norm_num)] at hq
      simp only
      rw [max_eq_right (by linarith [hq.2])]
    rw [this, int_lin2]
    nlinarith [sq_nonneg (d - 2)]

lemma int_max' (d : ℝ) : ∫ q in (0:ℝ)..2, max 0 (q - 2 - d) ≤ d ^ 2 / 2 := by
  have h := intervalIntegral.integral_comp_sub_left (fun x : ℝ => max 0 (-d - x)) (2 : ℝ)
    (a := 0) (b := 2)
  simp only [sub_self, sub_zero] at h
  have e : ∫ q in (0:ℝ)..2, max 0 (q - 2 - d) = ∫ x in (0:ℝ)..2, max 0 (-d - (2 - x)) := by
    congr 1; funext x; ring_nf
  rw [e, h]
  have := int_max (-d)
  simpa using this

end RAH
end RatingsAdvert.AdInterval


namespace RatingsAdvert.AdInterval
namespace RAH

open Set

/-- derivative of `g` -/
noncomputable def gp (P : Params) (x : ℝ) : ℝ := P.beta * (1 + P.beta * x - P.tau) / 2

lemma qe_eq (P : Params) (hb : 0 < P.beta) (q z ze : ℝ) :
    qe P q z ze = min (max 0 (q - P.tau * (z - ze) / P.beta)) 2 := by
  unfold qe
  congr 2
  field_simp

lemma pt_upper (P : Params) (hb : 0 < P.beta) (ht : P.tau < 1) (q d : ℝ) (hq : q ∈ Icc (0:ℝ) 2) :
    g P (min (max 0 (q - d)) 2) ≤
      g P q - gp P q * d + P.beta ^ 2 * d ^ 2 / 4 + gp P 2 * max 0 (d - q) := by
  unfold g gp
  obtain ⟨hq0, hq2⟩ := hq
  rcases le_total (q - d) 0 with h1 | h1
  · rw [max_eq_left h1, min_eq_left (by norm_num), max_eq_right (by linarith)]
    have hgq : 0 ≤ 1 + P.beta * q - P.tau := by nlinarith
    have : P.beta * (1 + P.beta * q - P.tau) ≤ P.beta * (1 + P.beta * 2 - P.tau) := by
      nlinarith [mul_nonneg (mul_nonneg hb.le hb.le) (by linarith : (0:ℝ) ≤ 2 - q)]
    nlinarith [mul_le_mul_of_nonneg_right this (by linarith : (0:ℝ) ≤ d - q), sq_nonneg (P.beta * q),
      sq_nonneg (P.beta * d), mul_nonneg hq0 (by linarith : (0:ℝ) ≤ d - q),
      mul_nonneg (mul_nonneg hb.le hb.le) (mul_nonneg hq0 (by linarith : (0:ℝ) ≤ d - q))]
  rcases le_total (q - d) 2 with h2 | h2
  · rw [max_eq_right h1, min_eq_left h2]
    have : 0 ≤ max 0 (d - q) := le_max_left _ _
    have : 0 ≤ P.beta * (1 + P.beta * 2 - P.tau) / 2 := by
      apply div_nonneg _ (by norm_num); apply mul_nonneg hb.le; nlinarith
    nlinarith [mul_nonneg this (le_max_left 0 (d - q))]
  · rw [max_eq_right h1, min_eq_right h2]
    have : 0 ≤ max 0 (d - q) := le_max_left _ _
    have h3 : 0 ≤ P.beta * (1 + P.beta * 2 - P.tau) / 2 := by
      apply div_nonneg _ (by norm_num); apply mul_nonneg hb.le; nlinarith
    have hgq : 0 ≤ 1 + P.beta * q - P.tau := by nlinarith
    have h4 : (2 - q) ^ 2 ≤ d ^ 2 := by nlinarith
    nlinarith [mul_nonneg h3 (le_max_left 0 (d - q)), mul_le_mul_of_nonneg_left h4 (sq_nonneg P.beta),
      mul_nonneg (mul_nonneg hb.le hgq) (by linarith : (0:ℝ) ≤ q - d - 2)]

lemma pt_lower (P : Params) (hb : 0 < P.beta) (ht : P.tau < 1) (q d : ℝ) (hq : q ∈ Icc (0:ℝ) 2) :
    g P q - gp P q * d - gp P 2 * max 0 (q - 2 - d) ≤ g P (min (max 0 (q - d)) 2) := by
  unfold g gp
  obtain ⟨hq0, hq2⟩ := hq
  have h3 : 0 ≤ P.beta * (1 + P.beta * 2 - P.tau) / 2 := by
    apply div_nonneg _ (by norm_num); apply mul_nonneg hb.le; nlinarith
  have hgq : 0 ≤ 1 + P.beta * q - P.tau := by nlinarith
  rcases le_total (q - d) 0 with h1 | h1
  · rw [max_eq_left h1, min_eq_left (by norm_num)]
    nlinarith [mul_nonneg h3 (le_max_left 0 (q - 2 - d)), sq_nonneg (P.beta * q),
      mul_nonneg (mul_nonneg hb.le hgq) (by linarith : (0:ℝ) ≤ d - q)]
  rcases le_total (q - d) 2 with h2 | h2
  · rw [max_eq_right h1, min_eq_left h2]
    nlinarith [mul_nonneg h3 (le_max_left 0 (q - 2 - d)), sq_nonneg (P.beta * d)]
  · rw [max_eq_right h1, min_eq_right h2, max_eq_right (by linarith : (0:ℝ) ≤ q - 2 - d)]
    have : P.beta * (1 + P.beta * q - P.tau) ≤ P.beta * (1 + P.beta * 2 - P.tau) := by
      nlinarith [mul_nonneg (mul_nonneg hb.le hb.le) (by linarith : (0:ℝ) ≤ 2 - q)]
    nlinarith [mul_le_mul_of_nonneg_right this (by linarith : (0:ℝ) ≤ q - 2 - d),
      sq_nonneg (P.beta * (2 - q))]

end RAH
end RatingsAdvert.AdInterval

namespace RatingsAdvert.AdInterval
namespace RAH

open Set

noncomputable def HAR (P : Params) (ze z' : ℝ) : ℝ := expQ (fun q => g P (qe P q z' ze))

lemma g_cont (P : Params) : Continuous (g P) := by unfold g; fun_prop

lemma gp_cont (P : Params) : Continuous (gp P) := by unfold gp; fun_prop

lemma int_gp (P : Params) : ∫ q in (0:ℝ)..2, gp P q = P.beta * (1 + P.beta - P.tau) := by
  have : (fun q => gp P q) = fun q => P.beta * (1 - P.tau) / 2 + P.beta ^ 2 / 2 * q := by
    funext q; unfold gp; ring
  rw [this, intervalIntegral.integral_add intervalIntegrable_const
    (intervalIntegral.intervalIntegrable_id.const_mul _), intervalIntegral.integral_const,
    intervalIntegral.integral_const_mul, integral_id]
  simp; ring

lemma HAR_self (P : Params) (hb : 0 < P.beta) (z : ℝ) :
    HAR P z z = (∫ q in (0:ℝ)..2, g P q) / 2 := by
  unfold HAR expQ
  congr 1
  apply intervalIntegral.integral_congr
  intro q hq
  rw [uIcc_of_le (by norm_num)] at hq
  simp only
  rw [qe_eq P hb, sub_self, mul_zero, zero_div, sub_zero, max_eq_right hq.1, min_eq_left hq.2]

lemma HAR_eq (P : Params) (hb : 0 < P.beta) (ze z' : ℝ) :
    HAR P ze z' = (∫ q in (0:ℝ)..2, g P (min (max 0 (q - P.tau * (z' - ze) / P.beta)) 2)) / 2 := by
  unfold HAR expQ
  simp_rw [qe_eq P hb]

lemma HAR_upper (P : Params) (hb : 0 < P.beta) (ht : P.tau < 1) (ze z' : ℝ) :
    HAR P ze z' ≤ HAR P ze ze - (P.tau * (z' - ze) / P.beta) * (P.beta * (1 + P.beta - P.tau)) / 2 +
      P.beta ^ 2 * (P.tau * (z' - ze) / P.beta) ^ 2 / 4 +
      gp P 2 * (P.tau * (z' - ze) / P.beta) ^ 2 / 4 := by
  set d := P.tau * (z' - ze) / P.beta
  rw [HAR_self P hb, HAR_eq P hb]
  have hc1 : Continuous fun q => g P (min (max 0 (q - d)) 2) := by
    have := g_cont P; fun_prop
  have hc2 : Continuous fun q => g P q - gp P q * d + P.beta ^ 2 * d ^ 2 / 4 + gp P 2 * max 0 (d - q) := by
    have := g_cont P; have := gp_cont P; fun_prop
  have hmono : ∫ q in (0:ℝ)..2, g P (min (max 0 (q - d)) 2) ≤
      ∫ q in (0:ℝ)..2, (g P q - gp P q * d + P.beta ^ 2 * d ^ 2 / 4 + gp P 2 * max 0 (d - q)) :=
    intervalIntegral.integral_mono_on (by norm_num) (hc1.intervalIntegrable _ _)
      (hc2.intervalIntegrable _ _) (fun q hq => pt_upper P hb ht q d hq)
  have hlin : ∫ q in (0:ℝ)..2, (g P q - gp P q * d + P.beta ^ 2 * d ^ 2 / 4 + gp P 2 * max 0 (d - q)) =
      (∫ q in (0:ℝ)..2, g P q) - (∫ q in (0:ℝ)..2, gp P q) * d + 2 * (P.beta ^ 2 * d ^ 2 / 4) +
        gp P 2 * ∫ q in (0:ℝ)..2, max 0 (d - q) := by
    have i1 := (g_cont P).intervalIntegrable (μ := MeasureTheory.volume) 0 2
    have i2 : IntervalIntegrable (fun q => gp P q * d) MeasureTheory.volume 0 2 :=
      ((gp_cont P).mul continuous_const).intervalIntegrable 0 2
    have i3 : Continuous fun q : ℝ => max 0 (d - q) := by fun_prop
    rw [intervalIntegral.integral_add, intervalIntegral.integral_add, intervalIntegral.integral_sub i1 i2,
      intervalIntegral.integral_mul_const, intervalIntegral.integral_const,
      intervalIntegral.integral_const_mul]
    · simp
    · exact i1.sub i2
    · exact intervalIntegrable_const
    · exact (i1.sub i2).add intervalIntegrable_const
    · exact (i3.intervalIntegrable _ _).const_mul _
  have hm := int_max d
  have hgp2 : 0 ≤ gp P 2 := by
    unfold gp; apply div_nonneg _ (by norm_num); apply mul_nonneg hb.le; nlinarith
  rw [int_gp] at hlin
  nlinarith [mul_le_mul_of_nonneg_left hm hgp2]

lemma HAR_lower (P : Params) (hb : 0 < P.beta) (ht : P.tau < 1) (ze z' : ℝ) :
    HAR P ze ze - (P.tau * (z' - ze) / P.beta) * (P.beta * (1 + P.beta - P.tau)) / 2 -
      gp P 2 * (P.tau * (z' - ze) / P.beta) ^ 2 / 4 ≤ HAR P ze z' := by
  set d := P.tau * (z' - ze) / P.beta
  rw [HAR_self P hb, HAR_eq P hb]
  have hc1 : Continuous fun q => g P (min (max 0 (q - d)) 2) := by
    have := g_cont P; fun_prop
  have hc2 : Continuous fun q => g P q - gp P q * d - gp P 2 * max 0 (q - 2 - d) := by
    have := g_cont P; have := gp_cont P; fun_prop
  have hmono : ∫ q in (0:ℝ)..2, (g P q - gp P q * d - gp P 2 * max 0 (q - 2 - d)) ≤
      ∫ q in (0:ℝ)..2, g P (min (max 0 (q - d)) 2) :=
    intervalIntegral.integral_mono_on (by norm_num) (hc2.intervalIntegrable _ _)
      (hc1.intervalIntegrable _ _) (fun q hq => pt_lower P hb ht q d hq)
  have hlin : ∫ q in (0:ℝ)..2, (g P q - gp P q * d - gp P 2 * max 0 (q - 2 - d)) =
      (∫ q in (0:ℝ)..2, g P q) - (∫ q in (0:ℝ)..2, gp P q) * d -
        gp P 2 * ∫ q in (0:ℝ)..2, max 0 (q - 2 - d) := by
    have i1 := (g_cont P).intervalIntegrable (μ := MeasureTheory.volume) 0 2
    have i2 : IntervalIntegrable (fun q => gp P q * d) MeasureTheory.volume 0 2 :=
      ((gp_cont P).mul continuous_const).intervalIntegrable 0 2
    have i3 : Continuous fun q : ℝ => max 0 (q - 2 - d) := by fun_prop
    rw [intervalIntegral.integral_sub, intervalIntegral.integral_sub i1 i2,
      intervalIntegral.integral_mul_const, intervalIntegral.integral_const_mul]
    · exact i1.sub i2
    · exact (i3.intervalIntegrable _ _).const_mul _
  have hm := int_max' d
  have hgp2 : 0 ≤ gp P 2 := by
    unfold gp; apply div_nonneg _ (by norm_num); apply mul_nonneg hb.le; nlinarith
  rw [int_gp] at hlin
  nlinarith [mul_le_mul_of_nonneg_left hm hgp2]

end RAH
end RatingsAdvert.AdInterval


namespace RatingsAdvert.AdInterval
namespace RAH

open Set Filter Asymptotics Topology

lemma hasDerivAt_of_quad (f : ℝ → ℝ) (x L M : ℝ)
    (h : ∀ y, |f y - f x - (y - x) * L| ≤ M * (y - x) ^ 2) : HasDerivAt f L x := by
  rw [hasDerivAt_iff_isLittleO]
  have h1 : (fun y => f y - f x - (y - x) • L) =O[𝓝 x] fun y => ‖y - x‖ ^ 2 := by
    apply IsBigO.of_bound M
    filter_upwards with y
    simp only [smul_eq_mul, Real.norm_eq_abs, norm_pow, sq_abs]
    exact h y
  exact h1.trans_isLittleO (isLittleO_pow_sub_sub x (m := 2) (by norm_num))

lemma HAR_deriv (P : Params) (hb : 0 < P.beta) (ht : P.tau < 1) (z : ℝ) :
    HasDerivAt (HAR P z) (-(P.tau * (1 + P.beta - P.tau) / 2)) z := by
  apply hasDerivAt_of_quad _ _ _ ((P.beta ^ 2 / 4 + gp P 2 / 4) * (P.tau / P.beta) ^ 2)
  intro y
  have hu := HAR_upper P hb ht z y
  have hl := HAR_lower P hb ht z y
  have e1 : P.tau * (y - z) / P.beta * (P.beta * (1 + P.beta - P.tau)) / 2 =
      (y - z) * (P.tau * (1 + P.beta - P.tau) / 2) := by field_simp
  have e2 : (P.tau * (y - z) / P.beta) ^ 2 = (P.tau / P.beta) ^ 2 * (y - z) ^ 2 := by
    field_simp
  rw [e1, e2] at hu hl
  have hgp2 : 0 ≤ gp P 2 := by
    unfold gp; apply div_nonneg _ (by norm_num); apply mul_nonneg hb.le; nlinarith
  have hsq : 0 ≤ (P.tau / P.beta) ^ 2 * (y - z) ^ 2 := by positivity
  rw [abs_le]
  constructor <;> nlinarith [mul_nonneg (sq_nonneg P.beta) hsq, mul_nonneg hgp2 hsq]

/-- the sufficiency bound for `HAR` -/
lemma HAR_suff (P : Params) (hS : P.Standing) (z y : ℝ) :
    HAR P z y - HAR P z z ≤ -(P.tau * (1 + P.beta - P.tau) / 2) * (y - z) +
      P.tau / P.beta * (y - z) ^ 2 / 2 := by
  obtain ⟨ht0, ht, hb, hb1, -⟩ := hS
  have hu := HAR_upper P hb (by linarith) z y
  have e1 : P.tau * (y - z) / P.beta * (P.beta * (1 + P.beta - P.tau)) / 2 =
      (y - z) * (P.tau * (1 + P.beta - P.tau) / 2) := by field_simp
  have e2 : (P.tau * (y - z) / P.beta) ^ 2 = P.tau / P.beta * (P.tau / P.beta * (y - z) ^ 2) := by
    field_simp
  rw [e1, e2] at hu
  have hk : 0 ≤ P.tau / P.beta * (y - z) ^ 2 := by positivity
  -- need (β²/4 + gp 2/4) * τ/β ≤ 1/2 * ... i.e. coefficient bound
  have hc : (P.beta ^ 2 / 4 + gp P 2 / 4) * (P.tau / P.beta) ≤ 1 / 2 := by
    unfold gp
    rw [show (P.beta ^ 2 / 4 + P.beta * (1 + P.beta * 2 - P.tau) / 2 / 4) * (P.tau / P.beta) =
      P.tau * (P.beta / 4 + (1 + P.beta * 2 - P.tau) / 8) by field_simp; ring]
    nlinarith
  have := mul_le_mul_of_nonneg_right hc hk
  nlinarith

/-! ## generic first-period equilibrium analysis -/

def EqCond (P : Params) (Hf : ℝ → ℝ) (z p1 : ℝ) : Prop :=
  ∀ z' ∈ Icc (0:ℝ) 1, ∀ p', p' * D1 P z' z p' + Hf z' - P.A z' ≤ p1 * D1 P z z p1 + Hf z - P.A z

lemma necessity (P : Params) (hS : P.Standing) (Hf : ℝ → ℝ) (L z p1 : ℝ) (hz : z ∈ Icc (0:ℝ) 1)
    (hE : EqCond P Hf z p1) (hH : HasDerivAt Hf L z)
    (h0 : deriv P.A 0 < ((1 + P.beta - 0 * P.tau) / 2) ^ 2 + L)
    (h1 : ((1 + P.beta - 1 * P.tau) / 2) ^ 2 + L < deriv P.A 1) :
    z ∈ Ioo (0:ℝ) 1 ∧ p1 = (1 + P.beta - z * P.tau) / 2 ∧
      ((1 + P.beta - z * P.tau) / 2) ^ 2 + L = deriv P.A z := by
  set K := (1 + P.beta - z * P.tau) / 2 with hK
  set F : ℝ → ℝ := fun y => y * K ^ 2 + Hf y - P.A y with hF
  have hmax : ∀ y ∈ Icc (0:ℝ) 1, F y ≤ F z := by
    intro y hy
    have a := hE y hy K
    rw [hK, D1_opt, ← hK] at a
    have b := D1_le P z z p1 hz.1
    rw [← hK] at b
    simp only [hF]
    linarith
  have hD : HasDerivAt F (1 * K ^ 2 + L - deriv P.A z) z :=
    (((hasDerivAt_id' z).mul_const _).add hH).sub (A_diff P hS z).hasDerivAt
  have hle : z < 1 → 1 * K ^ 2 + L - deriv P.A z ≤ 0 := fun hz1 =>
    deriv_nonpos_of_max_right F _ z 1 hz1 hD
      (fun y hy => hmax y ⟨le_trans hz.1 hy.1, hy.2⟩)
  have hge : 0 < z → 0 ≤ 1 * K ^ 2 + L - deriv P.A z := fun hz0 =>
    deriv_nonneg_of_max_left F _ 0 z hz0 hD
      (fun y hy => hmax y ⟨hy.1, le_trans hy.2 hz.2⟩)
  have hz0 : 0 < z := by
    rcases hz.1.lt_or_eq with h | h
    · exact h
    · exfalso
      subst h
      have := hle (by norm_num)
      rw [hK] at this
      linarith
  have hz1 : z < 1 := by
    rcases hz.2.lt_or_eq with h | h
    · exact h
    · exfalso
      subst h
      have := hge (by norm_num)
      rw [hK] at this
      linarith
  refine ⟨⟨hz0, hz1⟩, ?_, ?_⟩
  · apply p1_eq P z p1 hz0
    intro p'
    have := hE z hz p'
    linarith
  · have := hle hz1; have := hge hz0; linarith

lemma sufficiency (P : Params) (hS : P.Standing) (Hf : ℝ → ℝ) (L z : ℝ) (hz : z ∈ Icc (0:ℝ) 1)
    (hfoc : ((1 + P.beta - z * P.tau) / 2) ^ 2 + L = deriv P.A z)
    (hb : ∀ y ∈ Icc (0:ℝ) 1, Hf y - Hf z ≤ L * (y - z) + P.tau / P.beta * (y - z) ^ 2 / 2) :
    EqCond P Hf z ((1 + P.beta - z * P.tau) / 2) := by
  intro y hy p'
  have a := D1_le P y z p' hy.1
  have b := A_convex P hS z y hz hy
  have c := hb y hy
  rw [D1_opt]
  rw [← hfoc] at b
  nlinarith

/-! ## the three cases -/

lemma bench_iff (P : Params) (z p1 p2 : ℝ) :
    IsPBEBench P z p1 p2 ↔ z ∈ Icc (0:ℝ) 1 ∧ (∀ p, p * D2Bench P p ≤ p2 * D2Bench P p2) ∧
      EqCond P (fun _ => p2 * D2Bench P p2) z p1 := by
  unfold IsPBEBench EqCond piBench
  rfl

lemma rev_iff (P : Params) (z p1 : ℝ) (p2 : ℝ → ℝ) :
    IsPBERev P z p1 p2 ↔ z ∈ Icc (0:ℝ) 1 ∧
      (∀ x ∈ Icc (0:ℝ) 2, ∀ p, p * D2Info P x p ≤ p2 x * D2Info P x (p2 x)) ∧
      EqCond P (fun _ => expQ (fun q => p2 q * D2Info P q (p2 q))) z p1 := by
  unfold IsPBERev EqCond piRev
  rfl

lemma piAR_eq (P : Params) (p2 : ℝ → ℝ)
    (hp2 : ∀ x ∈ Icc (0:ℝ) 2, p2 x = (1 + P.beta * x - P.tau) / 2) (ze z' p' : ℝ) :
    piAR P p2 ze z' p' = p' * D1 P z' ze p' + HAR P ze z' - P.A z' := by
  unfold piAR HAR
  congr 3
  funext q
  exact p2_profit P _ _ (hp2 _ (qe_mem P q z' ze))

lemma ar_iff (P : Params) (z p1 : ℝ) (p2 : ℝ → ℝ)
    (hp2 : ∀ x ∈ Icc (0:ℝ) 2, p2 x = (1 + P.beta * x - P.tau) / 2) :
    IsPBEAR P z p1 p2 ↔ z ∈ Icc (0:ℝ) 1 ∧
      (∀ x ∈ Icc (0:ℝ) 2, ∀ p, p * D2Info P x p ≤ p2 x * D2Info P x (p2 x)) ∧
      EqCond P (HAR P z) z p1 := by
  unfold IsPBEAR EqCond
  simp only [piAR_eq P p2 hp2]

lemma p2_opt (P : Params) (x : ℝ) :
    ∀ p, p * D2Info P x p ≤ (1 + P.beta * x - P.tau) / 2 * D2Info P x ((1 + P.beta * x - P.tau) / 2) := by
  intro p; unfold D2Info; nlinarith [sq_nonneg (p - (1 + P.beta * x - P.tau) / 2)]

lemma p2_bench_opt (P : Params) :
    ∀ p, p * D2Bench P p ≤ (1 + P.beta - P.tau) / 2 * D2Bench P ((1 + P.beta - P.tau) / 2) := by
  intro p; unfold D2Bench; nlinarith [sq_nonneg (p - (1 + P.beta - P.tau) / 2)]

lemma c_pos (P : Params) (hS : P.Standing) : 0 < P.tau * (1 + P.beta - P.tau) / 2 := by
  obtain ⟨ht0, ht, hb, hb1, -⟩ := hS
  apply div_pos _ (by norm_num); apply mul_pos ht0; linarith

end RAH
end RatingsAdvert.AdInterval


namespace RatingsAdvert.AdInterval
namespace RAH

open Set

lemma phi_strict (P : Params) (hS : P.Standing) (x y : ℝ) (hx : x ∈ Icc (0:ℝ) 1)
    (hy : y ∈ Icc (0:ℝ) 1) (hxy : x < y) :
    ((1 + P.beta - y * P.tau) / 2) ^ 2 - deriv P.A y < ((1 + P.beta - x * P.tau) / 2) ^ 2 - deriv P.A x := by
  have hA := A'_strict P hS x y hx hy hxy
  obtain ⟨ht0, ht, hb, hb1, -⟩ := hS
  have h1 : 0 ≤ 1 + P.beta - y * P.tau := by nlinarith [hy.2]
  have h2 : 1 + P.beta - y * P.tau ≤ 1 + P.beta - x * P.tau := by nlinarith
  have : ((1 + P.beta - y * P.tau) / 2) ^ 2 ≤ ((1 + P.beta - x * P.tau) / 2) ^ 2 := by
    apply pow_le_pow_left₀ (by linarith) (by linarith)
  linarith

lemma root_lt (P : Params) (hS : P.Standing) (x y L M : ℝ) (hx : x ∈ Icc (0:ℝ) 1)
    (hy : y ∈ Icc (0:ℝ) 1) (hLM : L < M)
    (hxL : ((1 + P.beta - x * P.tau) / 2) ^ 2 + L = deriv P.A x)
    (hyM : ((1 + P.beta - y * P.tau) / 2) ^ 2 + M = deriv P.A y) : x < y := by
  by_contra h
  have h := not_lt.mp h
  rcases h.lt_or_eq with h | h
  · have := phi_strict P hS y x hy hx h; linarith
  · subst h; linarith

lemma root_eq (P : Params) (hS : P.Standing) (x y L : ℝ) (hx : x ∈ Icc (0:ℝ) 1)
    (hy : y ∈ Icc (0:ℝ) 1)
    (hxL : ((1 + P.beta - x * P.tau) / 2) ^ 2 + L = deriv P.A x)
    (hyL : ((1 + P.beta - y * P.tau) / 2) ^ 2 + L = deriv P.A y) : x = y := by
  rcases lt_trichotomy x y with h | h | h
  · have := phi_strict P hS x y hx hy h; linarith
  · exact h
  · have := phi_strict P hS y x hy hx h; linarith

lemma interior_h0 (P : Params) (hS : P.Standing) (hI : P.Interior) (L : ℝ)
    (hL : -(P.tau * (1 + P.beta - P.tau) / 2) ≤ L) :
    deriv P.A 0 < ((1 + P.beta - 0 * P.tau) / 2) ^ 2 + L := by
  have := hI.1
  simp only [zero_mul, sub_zero]
  linarith

lemma interior_h1 (P : Params) (hI : P.Interior) (L : ℝ) (hL : L ≤ 0) :
    ((1 + P.beta - 1 * P.tau) / 2) ^ 2 + L < deriv P.A 1 := by
  have := hI.2
  simp only [one_mul]
  linarith

theorem lemma_1' (P : Params) (hS : P.Standing) (hI : P.Interior) :
    (∀ z p1 p2 : ℝ, IsPBEBench P z p1 p2 →
        z ∈ Set.Ioo (0 : ℝ) 1 ∧ p1 = (1 + P.beta - z * P.tau) / 2 ∧
          p2 = (1 + P.beta - P.tau) / 2 ∧
          ((1 + P.beta - z * P.tau) / 2) ^ 2 = deriv P.A z) ∧
      ∀ z ∈ Set.Icc (0 : ℝ) 1, ((1 + P.beta - z * P.tau) / 2) ^ 2 = deriv P.A z →
        IsPBEBench P z ((1 + P.beta - z * P.tau) / 2) ((1 + P.beta - P.tau) / 2) := by
  have hc := c_pos P hS
  constructor
  · intro z p1 p2 h
    rw [bench_iff] at h
    obtain ⟨hz, hp2, hE⟩ := h
    obtain ⟨h1, h2, h3⟩ := necessity P hS _ 0 z p1 hz hE (hasDerivAt_const _ _)
      (interior_h0 P hS hI 0 (by linarith)) (interior_h1 P hI 0 le_rfl)
    exact ⟨h1, h2, p2_bench_eq P p2 hp2, by linarith⟩
  · intro z hz hfoc
    rw [bench_iff]
    refine ⟨hz, p2_bench_opt P, sufficiency P hS _ 0 z hz (by linarith) ?_⟩
    intro y hy
    have : 0 ≤ P.tau / P.beta * (y - z) ^ 2 / 2 := by
      have := hS.1; have := hS.2.2.1; positivity
    simp only [sub_self, zero_mul, zero_add]
    exact this

theorem ar_profit_deriv' (P : Params) (hS : P.Standing) (z : ℝ) (hz : z ∈ Set.Icc (0 : ℝ) 1) :
    HasDerivAt (fun z' : ℝ => expQ (fun q => ((1 + P.beta * qe P q z' z - P.tau) / 2) ^ 2))
      (-(P.tau * (1 + P.beta - P.tau) / 2)) z :=
  HAR_deriv P hS.2.2.1 (by linarith [hS.2.1]) z

/-- AR necessity, without the comparison -/
lemma ar_nec (P : Params) (hS : P.Standing) (hI : P.Interior) (z p1 : ℝ) (p2 : ℝ → ℝ)
    (h : IsPBEAR P z p1 p2) :
    z ∈ Set.Ioo (0 : ℝ) 1 ∧ p1 = (1 + P.beta - z * P.tau) / 2 ∧
      (∀ x ∈ Set.Icc (0 : ℝ) 2, p2 x = (1 + P.beta * x - P.tau) / 2) ∧
      ((1 + P.beta - z * P.tau) / 2) ^ 2 - P.tau * (1 + P.beta - P.tau) / 2 = deriv P.A z := by
  have hc := c_pos P hS
  have hp2 : ∀ x ∈ Set.Icc (0 : ℝ) 2, p2 x = (1 + P.beta * x - P.tau) / 2 :=
    fun x hx => p2_eq P x (p2 x) (h.2.1 x hx)
  rw [ar_iff P z p1 p2 hp2] at h
  obtain ⟨hz, -, hE⟩ := h
  obtain ⟨h1, h2, h3⟩ := necessity P hS _ _ z p1 hz hE
    (HAR_deriv P hS.2.2.1 (by linarith [hS.2.1]) z)
    (interior_h0 P hS hI _ le_rfl) (interior_h1 P hI _ (by linarith))
  exact ⟨h1, h2, hp2, by linarith⟩

lemma bench_nec (P : Params) (hS : P.Standing) (hI : P.Interior) (z p1 p2 : ℝ)
    (h : IsPBEBench P z p1 p2) :
    z ∈ Set.Ioo (0 : ℝ) 1 ∧ p1 = (1 + P.beta - z * P.tau) / 2 ∧
          p2 = (1 + P.beta - P.tau) / 2 ∧
          ((1 + P.beta - z * P.tau) / 2) ^ 2 = deriv P.A z :=
  (lemma_1' P hS hI).1 z p1 p2 h

theorem lemma_2' (P : Params) (hS : P.Standing) (hI : P.Interior) (z p1 : ℝ) (p2 : ℝ → ℝ)
    (h : IsPBEAR P z p1 p2) :
    z ∈ Set.Ioo (0 : ℝ) 1 ∧ p1 = (1 + P.beta - z * P.tau) / 2 ∧
      (∀ x ∈ Set.Icc (0 : ℝ) 2, p2 x = (1 + P.beta * x - P.tau) / 2) ∧
      ((1 + P.beta - z * P.tau) / 2) ^ 2 - P.tau * (1 + P.beta - P.tau) / 2 = deriv P.A z ∧
      ∀ z0 p10 p20 : ℝ, IsPBEBench P z0 p10 p20 → z < z0 ∧ p10 < p1 := by
  obtain ⟨h1, h2, h3, h4⟩ := ar_nec P hS hI z p1 p2 h
  refine ⟨h1, h2, h3, h4, ?_⟩
  intro z0 p10 p20 hB
  obtain ⟨g1, g2, -, g4⟩ := bench_nec P hS hI z0 p10 p20 hB
  have hc := c_pos P hS
  have hlt : z < z0 := root_lt P hS z z0 (-(P.tau * (1 + P.beta - P.tau) / 2)) 0
    (Ioo_subset_Icc_self h1) (Ioo_subset_Icc_self g1) (by linarith) (by linarith) (by linarith)
  refine ⟨hlt, ?_⟩
  rw [g2, h2]
  have := hS.1
  nlinarith

theorem lemma_2_sufficiency' (P : Params) (hS : P.Standing) (hI : P.Interior) (z : ℝ)
    (hz : z ∈ Set.Icc (0 : ℝ) 1)
    (h8 : ((1 + P.beta - z * P.tau) / 2) ^ 2 - P.tau * (1 + P.beta - P.tau) / 2 = deriv P.A z) :
    IsPBEAR P z ((1 + P.beta - z * P.tau) / 2) (fun x => (1 + P.beta * x - P.tau) / 2) := by
  rw [ar_iff P _ _ _ (fun x _ => rfl)]
  refine ⟨hz, fun x _ => p2_opt P x, sufficiency P hS _ (-(P.tau * (1 + P.beta - P.tau) / 2)) z hz
    (by linarith) ?_⟩
  intro y _
  exact HAR_suff P hS z y

theorem lemma_3' (P : Params) (hS : P.Standing) (hI : P.Interior) :
    (∀ (z p1 : ℝ) (p2 : ℝ → ℝ), IsPBERev P z p1 p2 →
        z ∈ Set.Ioo (0 : ℝ) 1 ∧ p1 = (1 + P.beta - z * P.tau) / 2 ∧
          (∀ x ∈ Set.Icc (0 : ℝ) 2, p2 x = (1 + P.beta * x - P.tau) / 2) ∧
          ((1 + P.beta - z * P.tau) / 2) ^ 2 = deriv P.A z ∧
          (∀ z0 p10 p20 : ℝ, IsPBEBench P z0 p10 p20 → z = z0 ∧ p1 = p10) ∧
          ∀ (zA p1A : ℝ) (p2A : ℝ → ℝ), IsPBEAR P zA p1A p2A → zA < z ∧ p1 < p1A) ∧
      ∀ z ∈ Set.Icc (0 : ℝ) 1, ((1 + P.beta - z * P.tau) / 2) ^ 2 = deriv P.A z →
        IsPBERev P z ((1 + P.beta - z * P.tau) / 2) (fun x => (1 + P.beta * x - P.tau) / 2) := by
  have hc := c_pos P hS
  constructor
  · intro z p1 p2 h
    have hp2 : ∀ x ∈ Set.Icc (0 : ℝ) 2, p2 x = (1 + P.beta * x - P.tau) / 2 :=
      fun x hx => p2_eq P x (p2 x) (h.2.1 x hx)
    rw [rev_iff] at h
    obtain ⟨hz, -, hE⟩ := h
    obtain ⟨h1, h2, h3⟩ := necessity P hS _ 0 z p1 hz hE (hasDerivAt_const _ _)
      (interior_h0 P hS hI 0 (by linarith)) (interior_h1 P hI 0 le_rfl)
    refine ⟨h1, h2, hp2, by linarith, ?_, ?_⟩
    · intro z0 p10 p20 hB
      obtain ⟨g1, g2, -, g4⟩ := bench_nec P hS hI z0 p10 p20 hB
      have : z = z0 := root_eq P hS z z0 0 (Ioo_subset_Icc_self h1) (Ioo_subset_Icc_self g1)
        h3 (by linarith)
      subst this
      exact ⟨rfl, by rw [h2, g2]⟩
    · intro zA p1A p2A hA
      obtain ⟨a1, a2, -, a4⟩ := ar_nec P hS hI zA p1A p2A hA
      have hlt : zA < z := root_lt P hS zA z (-(P.tau * (1 + P.beta - P.tau) / 2)) 0
        (Ioo_subset_Icc_self a1) (Ioo_subset_Icc_self h1) (by linarith) (by linarith) h3
      refine ⟨hlt, ?_⟩
      rw [h2, a2]
      have := hS.1
      nlinarith
  · intro z hz hfoc
    rw [rev_iff]
    refine ⟨hz, fun x _ => p2_opt P x, sufficiency P hS _ 0 z hz (by linarith) ?_⟩
    intro y hy
    have : 0 ≤ P.tau / P.beta * (y - z) ^ 2 / 2 := by
      have := hS.1; have := hS.2.2.1; positivity
    simp only [sub_self, zero_mul, zero_add]
    exact this

end RAH
end RatingsAdvert.AdInterval


open RatingsAdvert.AdInterval

theorem solution (P : Params) (hS : P.Standing) (hI : P.Interior) :
    (∀ z p1 p2 : ℝ, IsPBEBench P z p1 p2 →
        z ∈ Set.Ioo (0 : ℝ) 1 ∧ p1 = (1 + P.beta - z * P.tau) / 2 ∧
          p2 = (1 + P.beta - P.tau) / 2 ∧
          ((1 + P.beta - z * P.tau) / 2) ^ 2 = deriv P.A z) ∧
      ∀ z ∈ Set.Icc (0 : ℝ) 1, ((1 + P.beta - z * P.tau) / 2) ^ 2 = deriv P.A z →
        IsPBEBench P z ((1 + P.beta - z * P.tau) / 2) ((1 + P.beta - P.tau) / 2) :=
  RAH.lemma_1' P hS hI
