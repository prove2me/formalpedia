-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Information100.P56.diagonal_convexity
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-20T06:18:56.708242+00:00
-- url     : https://prove2.me/submissions/e91ecb1e-dc62-4b9a-9149-2223fb8b1b64

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P56

noncomputable section

open QAlgorithms.Papers.Independent.Information100.P56

open scoped ComplexConjugate ComplexOrder Matrix

attribute [local instance] Classical.propDecidable

lemma h54e_g {s : ℝ} (hs : |s| < 1) :
    HasDerivAt (fun s : ℝ => Real.binEntropy ((1 + s) / 2)) (-inverseTanh s) s := by
  have h1 := abs_lt.mp hs
  have hin : HasDerivAt (fun s : ℝ => (1 + s) / 2) (1/2) s := by
    simpa using ((hasDerivAt_id s).const_add 1).div_const 2
  have hb := Real.hasDerivAt_binEntropy (p := (1 + s) / 2) (by linarith) (by linarith)
  have := hb.comp s hin
  have e : (Real.log (1 - (1 + s) / 2) - Real.log ((1 + s) / 2)) * (1 / 2) = -inverseTanh s := by
    unfold inverseTanh
    have e1 : 1 - (1 + s) / 2 = (1 - s) / 2 := by ring
    rw [e1, Real.log_div (by linarith) (by norm_num), Real.log_div (by linarith) (by norm_num)]
    ring
  rw [e] at this
  exact this

lemma h54e_atanh {s : ℝ} (hs : |s| < 1) :
    HasDerivAt inverseTanh (1 / (1 - s ^ 2)) s := by
  have h1 := abs_lt.mp hs
  have ha : HasDerivAt (fun s : ℝ => Real.log (1 + s)) (1 / (1 + s)) s := by
    have := ((hasDerivAt_id s).const_add 1).log (by simp; linarith)
    simpa using this
  have hb : HasDerivAt (fun s : ℝ => Real.log (1 - s)) (-1 / (1 - s)) s := by
    have := ((hasDerivAt_id s).const_sub 1).log (by simp; linarith)
    simpa [neg_div] using this
  have := (ha.sub hb).div_const 2
  have e : (1 / (1 + s) - -1 / (1 - s)) / 2 = 1 / (1 - s ^ 2) := by
    have : (1 + s) ≠ 0 := by linarith
    have : (1 - s) ≠ 0 := by linarith
    have : (1 - s^2) ≠ 0 := by nlinarith
    field_simp
    ring
  rw [e] at this
  exact this

lemma h54e_R {u k z : ℝ} (hu : 0 < u) (hk : 0 ≤ k) :
    HasDerivAt (fun z : ℝ => Real.sqrt (u + k * z ^ 2)) (k * z / Real.sqrt (u + k * z ^ 2)) z := by
  have hpos : 0 < u + k * z ^ 2 := by positivity
  have hf : HasDerivAt (fun z : ℝ => u + k * z ^ 2) (k * (2 * z)) z := by
    have := ((hasDerivAt_pow 2 z).const_mul k).const_add u
    simpa using this
  have := hf.sqrt hpos.ne'
  have hs : Real.sqrt (u + k * z ^ 2) ≠ 0 := (Real.sqrt_pos.mpr hpos).ne'
  have e : k * (2 * z) / (2 * Real.sqrt (u + k * z ^ 2)) = k * z / Real.sqrt (u + k * z ^ 2) := by
    field_simp
  rw [e] at this
  exact this

lemma h54e_dom {p z : ℝ} (hp : 0 < p ∧ p < 1 / 2) (hz : |z| < 1) :
    0 < (1 - 2 * p) ^ 2 ∧ 0 < 1 - (1 - 2 * p) ^ 2 ∧ |(1 - 2 * p) * z| < 1 ∧
    0 < Real.sqrt ((1 - 2 * p) ^ 2 + (1 - (1 - 2 * p) ^ 2) * z ^ 2) ∧
    |Real.sqrt ((1 - 2 * p) ^ 2 + (1 - (1 - 2 * p) ^ 2) * z ^ 2)| < 1 := by
  obtain ⟨h0, h1⟩ := hp
  have hz2 : z ^ 2 < 1 := by
    have := abs_lt.mp hz; nlinarith
  have hz0 : 0 ≤ z ^ 2 := sq_nonneg z
  have ha0 : 0 < 1 - 2 * p := by linarith
  have ha1 : 1 - 2 * p < 1 := by linarith
  have hu : 0 < (1 - 2 * p) ^ 2 := by positivity
  have hu1 : (1 - 2 * p) ^ 2 < 1 := by nlinarith
  have hk : 0 < 1 - (1 - 2 * p) ^ 2 := by linarith
  refine ⟨hu, hk, ?_, ?_, ?_⟩
  · rw [abs_mul, abs_of_pos ha0]
    have := abs_nonneg z
    nlinarith
  · apply Real.sqrt_pos.mpr; positivity
  · rw [abs_of_nonneg (Real.sqrt_nonneg _)]
    rw [Real.sqrt_lt' (by norm_num)]
    nlinarith

def h54e_F1 (p z : ℝ) : ℝ :=
  -(1 - 2 * p) * inverseTanh ((1 - 2 * p) * z) +
    (1 - (1 - 2 * p) ^ 2) * z *
      inverseTanh (Real.sqrt ((1 - 2 * p) ^ 2 + (1 - (1 - 2 * p) ^ 2) * z ^ 2)) /
      Real.sqrt ((1 - 2 * p) ^ 2 + (1 - (1 - 2 * p) ^ 2) * z ^ 2)

lemma h54e_d1 {p z : ℝ} (hp : 0 < p ∧ p < 1 / 2) (hz : |z| < 1) :
    HasDerivAt (diagonalDelta p) (h54e_F1 p z) z := by
  obtain ⟨hu, hk, haz, hr0, hr1⟩ := h54e_dom hp hz
  set a := 1 - 2 * p
  set u := a ^ 2
  set k := 1 - u
  have hfun : diagonalDelta p = fun z => (fun s : ℝ => Real.binEntropy ((1 + s) / 2)) (a * z) -
      (fun s : ℝ => Real.binEntropy ((1 + s) / 2)) (Real.sqrt (u + k * z ^ 2)) := by
    funext z; rfl
  rw [hfun]
  have hA : HasDerivAt (fun z : ℝ => a * z) a z := by
    simpa using (hasDerivAt_id z).const_mul a
  have h1 := (h54e_g haz).comp z hA
  have h2 := (h54e_g hr1).comp z (h54e_R (z := z) hu hk.le)
  have := h1.sub h2
  have e : -inverseTanh (a * z) * a - -inverseTanh (Real.sqrt (u + k * z ^ 2)) *
      (k * z / Real.sqrt (u + k * z ^ 2)) = h54e_F1 p z := by
    unfold h54e_F1; ring
  rw [e] at this
  exact this

lemma h54e_alg (a k z r T : ℝ) (hr : r ≠ 0) (h1r : 1 - r ^ 2 ≠ 0) (haz : 1 - (a * z) ^ 2 ≠ 0)
    (hrr : r ^ 2 = a ^ 2 + k * z ^ 2) :
    -a * (1 / (1 - (a * z) ^ 2) * a) +
      ((k * T + k * z * (1 / (1 - r ^ 2) * (k * z / r))) * r - k * z * T * (k * z / r)) / r ^ 2 =
    -a ^ 2 / (1 - a ^ 2 * z ^ 2) + k * a ^ 2 * T / r ^ 3 + k ^ 2 * z ^ 2 / (r ^ 2 * (1 - r ^ 2)) := by
  have e1 : -a * (1 / (1 - (a * z) ^ 2) * a) +
      ((k * T + k * z * (1 / (1 - r ^ 2) * (k * z / r))) * r - k * z * T * (k * z / r)) / r ^ 2 =
      -a ^ 2 / (1 - a ^ 2 * z ^ 2) + k * (r ^ 2 - k * z ^ 2) * T / r ^ 3 +
        k ^ 2 * z ^ 2 / (r ^ 2 * (1 - r ^ 2)) := by
    have : 1 - a ^ 2 * z ^ 2 ≠ 0 := by rw [← mul_pow]; exact haz
    field_simp
    ring
  rw [e1, hrr]; ring

lemma h54e_d2 {p z : ℝ} (hp : 0 < p ∧ p < 1 / 2) (hz : |z| < 1) :
    let a := 1 - 2 * p
    let u := a ^ 2
    let k := 1 - u
    let t := z ^ 2
    let r := Real.sqrt (u + k * t)
    HasDerivAt (h54e_F1 p)
      (-u / (1 - u * t) + k * u * inverseTanh r / r ^ 3 +
        k ^ 2 * t / (r ^ 2 * (1 - r ^ 2))) z := by
  intro a u k t r
  obtain ⟨hu, hk, haz, hr0, hr1⟩ := h54e_dom hp hz
  have hA : HasDerivAt (fun z : ℝ => a * z) a z := by
    simpa using (hasDerivAt_id z).const_mul a
  have h1 := ((h54e_atanh haz).comp z hA).const_mul (-a)
  have hR := h54e_R (z := z) hu hk.le
  have h2 := (h54e_atanh hr1).comp z hR
  have hkz : HasDerivAt (fun z : ℝ => k * z) k z := by
    simpa using (hasDerivAt_id z).const_mul k
  have h3 := ((hkz.mul h2).div hR hr0.ne')
  have := h1.add h3
  have hrr : r ^ 2 = u + k * t := Real.sq_sqrt (by positivity)
  have hr0' : r ≠ 0 := hr0.ne'
  have habs := abs_lt.mp hr1
  have h1r : 1 - r ^ 2 ≠ 0 := by
    have : r < 1 := habs.2
    nlinarith
  have haz' := abs_lt.mp haz
  have h1az : 1 - (a * z) ^ 2 ≠ 0 := by
    have : (a * z) ^ 2 < 1 := by nlinarith
    linarith
  have e := h54e_alg a k z r (inverseTanh r) hr0' h1r h1az hrr
  exact this.congr_deriv e

lemma h54e_ev {p z : ℝ} (hp : 0 < p ∧ p < 1 / 2) (hz : |z| < 1) :
    deriv (diagonalDelta p) =ᶠ[nhds z] h54e_F1 p := by
  have hopen : IsOpen {w : ℝ | |w| < 1} := isOpen_lt continuous_abs continuous_const
  filter_upwards [hopen.mem_nhds hz] with w hw
  exact (h54e_d1 hp hw).deriv

lemma h54e_tan {a r : ℝ} (ha : 0 ≤ a) (har : a ≤ r) (hr : r < 1) :
    inverseTanh a + (r - a) / (1 - a ^ 2) ≤ inverseTanh r := by
  rcases eq_or_lt_of_le har with h | h
  · subst h; simp
  have hcont : ContinuousOn inverseTanh (Set.Icc a r) := by
    intro x hx
    have : |x| < 1 := by rw [abs_lt]; constructor <;> linarith [hx.1, hx.2]
    exact (h54e_atanh this).continuousAt.continuousWithinAt
  obtain ⟨c, hc, hcd⟩ := exists_hasDerivAt_eq_slope inverseTanh (fun s => 1 / (1 - s ^ 2)) h hcont
    (fun x hx => h54e_atanh (by rw [abs_lt]; constructor <;> linarith [hx.1, hx.2]))
  have hra : 0 < r - a := by linarith
  have hka : 0 < 1 - a ^ 2 := by nlinarith
  have hkc : 0 < 1 - c ^ 2 := by nlinarith [hc.1, hc.2]
  have hle : 1 / (1 - a ^ 2) ≤ 1 / (1 - c ^ 2) := by
    apply one_div_le_one_div_of_le hkc; nlinarith [hc.1, hc.2]
  rw [hcd, le_div_iff₀ hra] at hle
  have h2 : (r - a) / (1 - a ^ 2) = (1 / (1 - a ^ 2)) * (r - a) := by ring
  linarith
lemma h54e_w (w : ℝ) (_hw0 : 0 ≤ w) (hw : (1 - w) ^ 2 ≥ w ^ 3) (hw1 : w < 1) : w ≤ 58 / 100 := by
  by_contra h
  push Not at h
  nlinarith [mul_pos (by linarith : (0:ℝ) < w - 58/100) (by linarith : (0:ℝ) < w + 58/100)]

lemma h54e_c0 (w : ℝ) (hw0 : 0 ≤ w) (hw : w ≤ 58 / 100) : 0 ≤ 3 - 9*w + 9*w^2 - 5*w^3 + 2*w^4 := by
  nlinarith [sq_nonneg (w - 1/2), sq_nonneg (w^2 - w), mul_nonneg hw0 (sub_nonneg.2 hw),
    mul_nonneg (mul_nonneg hw0 hw0) (sub_nonneg.2 hw), mul_nonneg (mul_nonneg hw0 hw0) hw0]

lemma h54e_c1 (w : ℝ) (hw0 : 0 ≤ w) : 0 ≤ 3 - 11*w + 11*w^2 - 4*w^3 + 5*w^4 := by
  nlinarith [sq_nonneg (w - 1/2), sq_nonneg (w^2 - w), sq_nonneg (w^2 - 1/2), sq_nonneg (w^2 - w/2 - 1/4),
    sq_nonneg (2*w^2 - w - 1), mul_nonneg hw0 (sq_nonneg (w - 1/2))]

lemma h54e_Q (a r : ℝ) (ha : 0 < a) (hw : a ^ 2 ≤ 58 / 100) (har : a ≤ r) :
    0 ≤ a^2 * (r - a * (1 - a^2)) * (1 - r^2) * ((1 - a^2) + a^4 - a^2 * r^2) +
      (1 - a^2) * r * (r^2 - a^2) * ((1 - a^2) + a^4 - a^2 * r^2) -
      a^2 * (1 - a^2) * r^3 * (1 - r^2) := by
  set s := r - a with hs
  have hs0 : 0 ≤ s := by linarith
  have hr : r = a + s := by linarith
  have c0 := h54e_c0 (a^2) (sq_nonneg a) hw
  have c1 := h54e_c1 (a^2) (sq_nonneg a)
  have e : a^2 * (r - a * (1 - a^2)) * (1 - r^2) * ((1 - a^2) + a^4 - a^2 * r^2) +
      (1 - a^2) * r * (r^2 - a^2) * ((1 - a^2) + a^4 - a^2 * r^2) -
      a^2 * (1 - a^2) * r^3 * (1 - r^2) =
      s * (a^2 * (3 - 9*(a^2) + 9*(a^2)^2 - 5*(a^2)^3 + 2*(a^2)^4) +
        a * (3 - 11*(a^2) + 11*(a^2)^2 - 4*(a^2)^3 + 5*(a^2)^4) * s +
        ((1 - 2 * a^2)^2 + 3 * a^6 + 4 * a^8) * s^2 + (4 * a^5 + a^7) * s^3 + a^4 * s^4) := by
    rw [hr]; ring
  rw [e]
  apply mul_nonneg hs0
  have : 0 ≤ (1 - 2 * a^2)^2 + 3 * a^6 + 4 * a^8 := by positivity
  have : 0 ≤ (4 * a^5 + a^7) * s^3 := by positivity
  have : 0 ≤ a^4 * s^4 := by positivity
  have : 0 ≤ a^2 * (3 - 9*(a^2) + 9*(a^2)^2 - 5*(a^2)^3 + 2*(a^2)^4) := mul_nonneg (sq_nonneg a) c0
  have : 0 ≤ a * (3 - 11*(a^2) + 11*(a^2)^2 - 4*(a^2)^3 + 5*(a^2)^4) * s :=
    mul_nonneg (mul_nonneg ha.le c1) hs0
  have : 0 ≤ ((1 - 2 * a^2)^2 + 3 * a^6 + 4 * a^8) * s^2 := by positivity
  linarith

lemma h54e_F2nn {a z : ℝ} (ha0 : 0 < a) (ha1 : a < 1) (hz : |z| < 1) (hw : a ^ 2 ≤ 58 / 100)
    (hf : (1 - a ^ 2) * inverseTanh a ≥ a ^ 3) :
    0 ≤ -a ^ 2 / (1 - a ^ 2 * z ^ 2) +
      (1 - a ^ 2) * a ^ 2 * inverseTanh (Real.sqrt (a ^ 2 + (1 - a ^ 2) * z ^ 2)) /
        Real.sqrt (a ^ 2 + (1 - a ^ 2) * z ^ 2) ^ 3 +
      (1 - a ^ 2) ^ 2 * z ^ 2 / (Real.sqrt (a ^ 2 + (1 - a ^ 2) * z ^ 2) ^ 2 *
        (1 - Real.sqrt (a ^ 2 + (1 - a ^ 2) * z ^ 2) ^ 2)) := by
  set r := Real.sqrt (a ^ 2 + (1 - a ^ 2) * z ^ 2) with hrdef
  have hk : 0 < 1 - a ^ 2 := by nlinarith
  have hz2 : z ^ 2 < 1 := by have := abs_lt.mp hz; nlinarith
  have hz0 : 0 ≤ z ^ 2 := sq_nonneg z
  have hrr : r ^ 2 = a ^ 2 + (1 - a ^ 2) * z ^ 2 := Real.sq_sqrt (by positivity)
  have hr0 : 0 ≤ r := Real.sqrt_nonneg _
  have har : a ≤ r := by
    rw [hrdef]; apply Real.le_sqrt_of_sq_le; nlinarith
  have hrpos : 0 < r := lt_of_lt_of_le ha0 har
  have hr1 : r < 1 := by nlinarith
  have h1r : 0 < 1 - r ^ 2 := by nlinarith
  have hut : 0 < 1 - a ^ 2 * z ^ 2 := by nlinarith
  -- lower bound on artanh
  have hT := h54e_tan ha0.le har hr1
  have hL : (a ^ 3 + r - a) / (1 - a ^ 2) ≤ inverseTanh r := by
    have : a ^ 3 / (1 - a ^ 2) ≤ inverseTanh a := by
      rw [div_le_iff₀ hk]; linarith
    have e : (a ^ 3 + r - a) / (1 - a ^ 2) = a ^ 3 / (1 - a ^ 2) + (r - a) / (1 - a ^ 2) := by ring
    linarith
  have hmono : (1 - a ^ 2) * a ^ 2 * ((a ^ 3 + r - a) / (1 - a ^ 2)) / r ^ 3 ≤
      (1 - a ^ 2) * a ^ 2 * inverseTanh r / r ^ 3 := by
    apply div_le_div_of_nonneg_right _ (by positivity)
    exact mul_le_mul_of_nonneg_left hL (by positivity)
  suffices h : 0 ≤ -a ^ 2 / (1 - a ^ 2 * z ^ 2) +
      (1 - a ^ 2) * a ^ 2 * ((a ^ 3 + r - a) / (1 - a ^ 2)) / r ^ 3 +
      (1 - a ^ 2) ^ 2 * z ^ 2 / (r ^ 2 * (1 - r ^ 2)) by linarith
  have ht : z ^ 2 = (r ^ 2 - a ^ 2) / (1 - a ^ 2) := by
    rw [eq_div_iff hk.ne']; linarith
  have hD : 0 < (1 - a ^ 2) + a ^ 4 - a ^ 2 * r ^ 2 := by
    have : (1 - a ^ 2) + a ^ 4 - a ^ 2 * r ^ 2 = (1 - a ^ 2) * (1 - a ^ 2 * z ^ 2) := by
      rw [hrr]; ring
    rw [this]; positivity
  have hQ := h54e_Q a r ha0 hw har
  have e : -a ^ 2 / (1 - a ^ 2 * z ^ 2) +
      (1 - a ^ 2) * a ^ 2 * ((a ^ 3 + r - a) / (1 - a ^ 2)) / r ^ 3 +
      (1 - a ^ 2) ^ 2 * z ^ 2 / (r ^ 2 * (1 - r ^ 2)) =
      (a^2 * (r - a * (1 - a^2)) * (1 - r^2) * ((1 - a^2) + a^4 - a^2 * r^2) +
      (1 - a^2) * r * (r^2 - a^2) * ((1 - a^2) + a^4 - a^2 * r^2) -
      a^2 * (1 - a^2) * r^3 * (1 - r^2)) /
      (((1 - a ^ 2) + a ^ 4 - a ^ 2 * r ^ 2) * r ^ 3 * (1 - r ^ 2)) := by
    rw [ht]
    have hut' : 1 - a ^ 2 * ((r ^ 2 - a ^ 2) / (1 - a ^ 2)) ≠ 0 := by
      rw [← ht]; exact hut.ne'
    have e2 : 1 - a ^ 2 * ((r ^ 2 - a ^ 2) / (1 - a ^ 2)) =
        ((1 - a ^ 2) + a ^ 4 - a ^ 2 * r ^ 2) / (1 - a ^ 2) := by
      field_simp; ring
    rw [e2]
    have := hk.ne'; have := hD.ne'; have := hrpos.ne'; have := h1r.ne'
    field_simp
    ring
  rw [e]
  apply div_nonneg hQ
  positivity

/-- Lemma VIII.3, pp.23–24: sufficient convexity criterion, including nonnegative
second derivative on the whole open interval and convexity on the closed interval. -/
theorem solution (p : ℝ) (hp : 0 < p ∧ p < 1 / 2)
    (hfirst : (1 - (1 - 2 * p) ^ 2) * inverseTanh (1 - 2 * p) ≥ (1 - 2 * p) ^ 3)
    (hsecond : (1 - (1 - 2 * p) ^ 2) ^ 2 ≥ ((1 - 2 * p) ^ 2) ^ 3) :
    (∀ z : ℝ, |z| < 1 → 0 ≤ deriv (deriv (diagonalDelta p)) z) ∧
    ConvexOn ℝ (Set.Icc (-1 : ℝ) 1) (diagonalDelta p) := by
  have ha0 : 0 < 1 - 2 * p := by linarith [hp.2]
  have ha1 : 1 - 2 * p < 1 := by linarith [hp.1]
  have hu1 : (1 - 2 * p) ^ 2 < 1 := by nlinarith
  have hw := h54e_w ((1 - 2 * p) ^ 2) (sq_nonneg _) hsecond hu1
  have hnn : ∀ z : ℝ, |z| < 1 → 0 ≤ deriv (deriv (diagonalDelta p)) z := by
    intro z hz
    rw [((h54e_d2 hp hz).congr_of_eventuallyEq (h54e_ev hp hz)).deriv]
    exact h54e_F2nn ha0 ha1 hz hw hfirst
  refine ⟨hnn, ?_⟩
  have hint : interior (Set.Icc (-1 : ℝ) 1) = {w : ℝ | |w| < 1} := by
    rw [interior_Icc]; ext w; simp [abs_lt]
  apply convexOn_of_deriv2_nonneg (convex_Icc _ _)
  · apply Continuous.continuousOn
    unfold diagonalDelta
    fun_prop
  · rw [hint]; intro w hw
    exact (h54e_d1 hp hw).differentiableAt.differentiableWithinAt
  · rw [hint]; intro w hw
    exact ((h54e_d2 hp hw).congr_of_eventuallyEq (h54e_ev hp hw)).differentiableAt.differentiableWithinAt
  · rw [hint]; intro w hw
    simpa using hnn w hw

end
