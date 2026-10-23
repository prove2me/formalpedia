-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Information100.P08.rectangleMinorants
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-22T12:58:11.564373+00:00
-- url     : https://prove2.me/submissions/74bff5a6-b942-4520-973a-6e0fbbd8bc42

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P08
namespace QAlgorithms.Papers.Independent.Information100.P08

open scoped Matrix ComplexConjugate ComplexOrder

noncomputable section

attribute [local instance] Classical.propDecidable

lemma x8_C : thermalConcurrence (1 / 2) (1 / 10) = certificateC := by
  have h1 : Real.sqrt (1 - 1 / 2) = 1 / Real.sqrt 2 := by
    rw [show (1 : ℝ) - 1 / 2 = 2⁻¹ by norm_num, Real.sqrt_inv, one_div]
  have h2 : Real.sqrt (1 / 10 * (1 - 1 / 10)) = 3 / 10 := by
    rw [show (1 : ℝ) / 10 * (1 - 1 / 10) = (3 / 10) ^ 2 by norm_num]
    exact Real.sqrt_sq (by norm_num)
  have h3 : (1 : ℝ) < Real.sqrt 2 := by
    rw [show (1 : ℝ) = Real.sqrt 1 by simp]
    exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
  have h4 : (1 : ℝ) / 2 < 1 / Real.sqrt 2 := by
    rw [div_lt_div_iff₀ (by norm_num) (by linarith)]
    nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
  unfold thermalConcurrence certificateC
  rw [h1, h2, max_eq_left (by linarith)]
  ring

lemma x8_Cpos : 0 < certificateC ∧ certificateC < 1 := by
  have h3 : (1 : ℝ) < Real.sqrt 2 := by
    rw [show (1 : ℝ) = Real.sqrt 1 by simp]
    exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
  have h4 : (1 : ℝ) / 2 < 1 / Real.sqrt 2 := by
    rw [div_lt_div_iff₀ (by norm_num) (by linarith)]
    nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
  have h5 : 1 / Real.sqrt 2 < 1 := by
    rw [div_lt_one (by linarith)]; exact h3
  unfold certificateC
  constructor <;> linarith

lemma x8_res (t u : ℝ) : certificateResidual t u =
    determinantEntropy (u / 2 + rectangleC t) - determinantEntropy (certificateC ^ 2 * u) -
      certificateAlpha - certificateBeta * (t - 1 / 2) := by
  unfold certificateResidual thermalPenalty
  rw [x8_C]
  congr 3
  unfold thermalDelta rectangleC
  ring_nf

lemma x8_mono {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) :
    determinantEntropy a ≤ determinantEntropy b := by
  unfold determinantEntropy binEntropy2
  apply div_le_div_of_nonneg_right _ (Real.log_nonneg (by norm_num))
  have hs : ∀ v : ℝ, 0 ≤ v → Real.sqrt (1 - 4 * v) ≤ 1 := fun v hv => by
    rw [Real.sqrt_le_one]; linarith
  apply Real.binEntropy_strictMonoOn.monotoneOn
  · constructor
    · linarith [hs a ha]
    · linarith [Real.sqrt_nonneg (1 - 4 * a)]
  · constructor
    · linarith [hs b (ha.trans hab)]
    · linarith [Real.sqrt_nonneg (1 - 4 * b)]
  · have : Real.sqrt (1 - 4 * b) ≤ Real.sqrt (1 - 4 * a) := Real.sqrt_le_sqrt (by linarith)
    linarith

lemma x8_hasDeriv {v : ℝ} (h0 : 0 < v) (h1 : v < 1 / 4) :
    HasDerivAt determinantEntropy (determinantEntropyDerivative v) v := by
  set s := Real.sqrt (1 - 4 * v) with hs
  have hs0 : 0 < s := Real.sqrt_pos.2 (by linarith)
  have hs1 : s < 1 := by
    rw [hs, Real.sqrt_lt' (by norm_num)]; linarith
  have hsq : HasDerivAt (fun y => Real.sqrt (1 - 4 * y)) (-4 / (2 * s)) v := by
    have := ((hasDerivAt_id' v).const_mul 4).const_sub 1
    have := this.sqrt (by simp; linarith)
    exact this.congr_deriv (by rw [← hs]; ring)
  have hp := (hsq.const_sub 1).div_const 2
  have hb := Real.hasDerivAt_binEntropy (p := (1 - s) / 2) (by
    intro h; linarith) (by intro h; linarith)
  have := (hb.comp v hp).div_const (Real.log 2)
  unfold determinantEntropy binEntropy2
  refine this.congr_deriv ?_
  unfold determinantEntropyDerivative inverseTanh
  rw [← hs]
  have hl : Real.log (1 - (1 - s) / 2) - Real.log ((1 - s) / 2) = Real.log ((1 + s) / (1 - s)) := by
    rw [← Real.log_div (by linarith) (by linarith)]
    congr 1
    field_simp
    ring
  rw [hl]
  have : Real.log 2 ≠ 0 := by positivity
  field_simp
  ring

lemma x8_cmin {tl th t : ℝ} (h1 : tl ≤ t) (h2 : t ≤ th) :
    rectangleC (max tl (min (1 / 10) th)) ≤ rectangleC t := by
  unfold rectangleC
  rcases le_total (1 / 10 : ℝ) th with h | h
  · rw [min_eq_left h]
    rcases le_total tl (1 / 10) with h' | h'
    · rw [max_eq_right h']; nlinarith
    · rw [max_eq_left h']; nlinarith
  · rw [min_eq_right h, max_eq_right (by linarith)]; nlinarith

lemma x8_cmax {tl th t : ℝ} (h1 : tl ≤ t) (h2 : t ≤ th) :
    rectangleC t ≤ max (rectangleC tl) (rectangleC th) := by
  unfold rectangleC
  rcases le_total t (1 / 10) with h | h
  · exact le_max_of_le_left (by nlinarith)
  · exact le_max_of_le_right (by nlinarith)

lemma x8_cpos (t : ℝ) : 0 < rectangleC t := by unfold rectangleC; positivity

lemma x8_dt (t u : ℝ) (h0 : 0 < u / 2 + rectangleC t) (h1 : u / 2 + rectangleC t < 1 / 4) :
    HasDerivAt (fun x => certificateResidual x u)
      ((t - 1 / 10) / 2 * determinantEntropyDerivative (u / 2 + rectangleC t) - certificateBeta) t := by
  have hf : (fun x => certificateResidual x u) = fun x =>
      determinantEntropy (u / 2 + rectangleC x) - determinantEntropy (certificateC ^ 2 * u) -
        certificateAlpha - certificateBeta * (x - 1 / 2) := funext fun x => x8_res x u
  rw [hf]
  have hc : HasDerivAt (fun x => u / 2 + rectangleC x) ((t - 1 / 10) / 2) t := by
    unfold rectangleC
    have := ((((hasDerivAt_id' t).sub_const (1 / 10)).pow 2).div_const 4).const_add (9 / 200)
    have := this.const_add (u / 2)
    exact this.congr_deriv (by ring)
  have := (((x8_hasDeriv h0 h1).comp t hc).sub_const (determinantEntropy (certificateC ^ 2 * u))).sub_const
    certificateAlpha
  have := this.sub (((hasDerivAt_id' t).sub_const (1 / 2)).const_mul certificateBeta)
  exact this.congr_deriv (by ring)

lemma x8_du (t u : ℝ) (h0 : 0 < u / 2 + rectangleC t) (h1 : u / 2 + rectangleC t < 1 / 4)
    (h2 : 0 < certificateC ^ 2 * u) (h3 : certificateC ^ 2 * u < 1 / 4) :
    HasDerivAt (fun x => certificateResidual t x)
      (determinantEntropyDerivative (u / 2 + rectangleC t) / 2 -
        certificateC ^ 2 * determinantEntropyDerivative (certificateC ^ 2 * u)) u := by
  have hf : (fun x => certificateResidual t x) = fun x =>
      determinantEntropy (x / 2 + rectangleC t) - determinantEntropy (certificateC ^ 2 * x) -
        certificateAlpha - certificateBeta * (t - 1 / 2) := funext fun x => x8_res t x
  rw [hf]
  have ha : HasDerivAt (fun x : ℝ => x / 2 + rectangleC t) (1 / 2) u := by
    exact ((hasDerivAt_id' u).div_const 2).add_const (rectangleC t)
  have hb : HasDerivAt (fun x : ℝ => certificateC ^ 2 * x) (certificateC ^ 2) u := by
    exact ((hasDerivAt_id' u).const_mul (certificateC ^ 2)).congr_deriv (by ring)
  have := (((x8_hasDeriv h0 h1).comp u ha).sub ((x8_hasDeriv h2 h3).comp u hb)).sub_const
    certificateAlpha
  have := this.sub_const (certificateBeta * (t - 1 / 2))
  exact this.congr_deriv (by ring)

theorem x8_main (tl th ul uh : ℝ)
    (ht : 0 ≤ tl ∧ tl ≤ th ∧ th ≤ 1) (hu : 0 ≤ ul ∧ ul ≤ uh ∧ uh ≤ 1 / 4) :
    let cm := rectangleC (max tl (min (1 / 10) th))
    let cp := max (rectangleC tl) (rectangleC th)
    (∀ t ∈ Set.Icc tl th, ∀ u ∈ Set.Icc ul uh, u ≤ t * (1 - t) →
      determinantEntropy (ul / 2 + cm) - determinantEntropy (certificateC ^ 2 * uh) -
        certificateAlpha - certificateBeta * (th - 1 / 2) ≤ certificateResidual t u) ∧
    ((0 < ul ∧ uh / 2 + cp < 1 / 4) →
      (∀ t ∈ Set.Icc tl th, ∀ u ∈ Set.Icc ul uh,
        deriv (fun x => certificateResidual x u) t =
          (t - 1 / 10) / 2 * determinantEntropyDerivative (u / 2 + rectangleC t) - certificateBeta ∧
        deriv (fun x => certificateResidual t x) u =
          determinantEntropyDerivative (u / 2 + rectangleC t) / 2 -
            certificateC ^ 2 * determinantEntropyDerivative (certificateC ^ 2 * u)) ∧
      (∀ Gt Gu : ℝ, 0 ≤ Gt → 0 ≤ Gu →
        (∀ t ∈ Set.Icc tl th, ∀ u ∈ Set.Icc ul uh,
          |deriv (fun x => certificateResidual x u) t| ≤ Gt) →
        (∀ t ∈ Set.Icc tl th, ∀ u ∈ Set.Icc ul uh,
          |deriv (fun x => certificateResidual t x) u| ≤ Gu) →
        ∀ t ∈ Set.Icc tl th, ∀ u ∈ Set.Icc ul uh,
          certificateResidual ((tl + th) / 2) ((ul + uh) / 2) -
            Gt * (th - tl) / 2 - Gu * (uh - ul) / 2 ≤ certificateResidual t u)) := by
  intro cm cp
  obtain ⟨hC0, hC1⟩ := x8_Cpos
  have hβ : (0 : ℝ) < certificateBeta := by unfold certificateBeta; norm_num
  refine ⟨?_, ?_⟩
  · rintro t ⟨ht1, ht2⟩ u ⟨hu1, hu2⟩ _
    rw [x8_res]
    have e1 : determinantEntropy (ul / 2 + cm) ≤ determinantEntropy (u / 2 + rectangleC t) :=
      x8_mono (add_nonneg (by linarith [hu.1]) (le_of_lt (x8_cpos _)))
        (by have := x8_cmin (th := th) ht1 ht2; linarith)
    have e2 : determinantEntropy (certificateC ^ 2 * u) ≤ determinantEntropy (certificateC ^ 2 * uh) :=
      x8_mono (mul_nonneg (sq_nonneg _) (by linarith [hu.1])) (mul_le_mul_of_nonneg_left hu2 (by positivity))
    nlinarith
  · rintro ⟨hul, hcp⟩
    have key : ∀ t ∈ Set.Icc tl th, ∀ u ∈ Set.Icc ul uh,
        HasDerivAt (fun x => certificateResidual x u)
          ((t - 1 / 10) / 2 * determinantEntropyDerivative (u / 2 + rectangleC t) - certificateBeta) t ∧
        HasDerivAt (fun x => certificateResidual t x)
          (determinantEntropyDerivative (u / 2 + rectangleC t) / 2 -
            certificateC ^ 2 * determinantEntropyDerivative (certificateC ^ 2 * u)) u := by
      rintro t ⟨ht1, ht2⟩ u ⟨hu1, hu2⟩
      have := x8_cmax ht1 ht2
      have := x8_cpos t
      have h0 : 0 < u / 2 + rectangleC t := by linarith
      have h1 : u / 2 + rectangleC t < 1 / 4 := by
        have : cp = max (rectangleC tl) (rectangleC th) := rfl
        linarith
      have h2 : 0 < certificateC ^ 2 * u := mul_pos (by positivity) (by linarith)
      have h3 : certificateC ^ 2 * u < 1 / 4 := by
        have : certificateC ^ 2 < 1 := by nlinarith
        nlinarith
      exact ⟨x8_dt t u h0 h1, x8_du t u h0 h1 h2 h3⟩
    refine ⟨fun t ht u hu => ⟨(key t ht u hu).1.deriv, (key t ht u hu).2.deriv⟩, ?_⟩
    intro Gt Gu hGt0 hGu0 hGt hGu t ht u hu
    have ht0 : (tl + th) / 2 ∈ Set.Icc tl th := ⟨by linarith, by linarith⟩
    have hu0 : (ul + uh) / 2 ∈ Set.Icc ul uh := ⟨by linarith, by linarith⟩
    have a := Convex.norm_image_sub_le_of_norm_deriv_le (f := fun x => certificateResidual x u)
      (fun x hx => (key x hx u hu).1.differentiableAt) (fun x hx => by
        rw [Real.norm_eq_abs]; exact hGt x hx u hu) (convex_Icc tl th) ht0 ht
    have b := Convex.norm_image_sub_le_of_norm_deriv_le
      (f := fun x => certificateResidual ((tl + th) / 2) x)
      (fun x hx => (key _ ht0 x hx).2.differentiableAt) (fun x hx => by
        rw [Real.norm_eq_abs]; exact hGu _ ht0 x hx) (convex_Icc ul uh) hu0 hu
    simp only [Real.norm_eq_abs] at a b
    have c1 : |t - (tl + th) / 2| ≤ (th - tl) / 2 := by
      rw [abs_le]; constructor <;> linarith [ht.1, ht.2]
    have c2 : |u - (ul + uh) / 2| ≤ (uh - ul) / 2 := by
      rw [abs_le]; constructor <;> linarith [hu.1, hu.2]
    have d1 := mul_le_mul_of_nonneg_left c1 hGt0
    have d2 := mul_le_mul_of_nonneg_left c2 hGu0
    have a' := (abs_le.1 (a.trans d1)).1
    have b' := (abs_le.1 (b.trans d2)).1
    linarith

end

end QAlgorithms.Papers.Independent.Information100.P08

open QAlgorithms.Papers.Independent.Information100.P08 in
theorem solution (tl th ul uh : ℝ)
    (ht : 0 ≤ tl ∧ tl ≤ th ∧ th ≤ 1) (hu : 0 ≤ ul ∧ ul ≤ uh ∧ uh ≤ 1 / 4) :
    let cm := rectangleC (max tl (min (1 / 10) th))
    let cp := max (rectangleC tl) (rectangleC th)
    (∀ t ∈ Set.Icc tl th, ∀ u ∈ Set.Icc ul uh, u ≤ t * (1 - t) →
      determinantEntropy (ul / 2 + cm) - determinantEntropy (certificateC ^ 2 * uh) -
        certificateAlpha - certificateBeta * (th - 1 / 2) ≤ certificateResidual t u) ∧
    ((0 < ul ∧ uh / 2 + cp < 1 / 4) →
      (∀ t ∈ Set.Icc tl th, ∀ u ∈ Set.Icc ul uh,
        deriv (fun x => certificateResidual x u) t =
          (t - 1 / 10) / 2 * determinantEntropyDerivative (u / 2 + rectangleC t) - certificateBeta ∧
        deriv (fun x => certificateResidual t x) u =
          determinantEntropyDerivative (u / 2 + rectangleC t) / 2 -
            certificateC ^ 2 * determinantEntropyDerivative (certificateC ^ 2 * u)) ∧
      (∀ Gt Gu : ℝ, 0 ≤ Gt → 0 ≤ Gu →
        (∀ t ∈ Set.Icc tl th, ∀ u ∈ Set.Icc ul uh,
          |deriv (fun x => certificateResidual x u) t| ≤ Gt) →
        (∀ t ∈ Set.Icc tl th, ∀ u ∈ Set.Icc ul uh,
          |deriv (fun x => certificateResidual t x) u| ≤ Gu) →
        ∀ t ∈ Set.Icc tl th, ∀ u ∈ Set.Icc ul uh,
          certificateResidual ((tl + th) / 2) ((ul + uh) / 2) -
            Gt * (th - tl) / 2 - Gu * (uh - ul) / 2 ≤ certificateResidual t u)) :=
  x8_main tl th ul uh ht hu
