-- Prove2me | solution 1 for PersPricingDist.PersonalA.pp_cutoff
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-22T18:41:44.495236+00:00
-- url     : https://prove2.me/submissions/e22a9bb2-a196-4cfb-8095-56b863fae74b

import Mathlib
import Definitions.Def_PersPricingDist_PersonalA_Setting

open PersPricingDist.PersonalA

namespace PPDAPPCutAux

theorem EF_lin (a b c d : ℝ) :
    ∫ x in c..d, (a - b * x) = a * (d - c) - b * (d ^ 2 - c ^ 2) / 2 := by
  rw [intervalIntegral.integral_sub (by simp) (by apply Continuous.intervalIntegrable; fun_prop)]
  rw [intervalIntegral.integral_const_mul]
  simp [integral_id]
  ring

lemma uA_of_le (M : Model) {x : ℝ} (hx : x ≤ 1) : M.uA x = 1 - x := by
  unfold Model.uA; exact max_eq_left (by linarith)

lemma uA_of_ge (M : Model) {x : ℝ} (hx : 1 ≤ x) : M.uA x = 0 := by
  unfold Model.uA; exact max_eq_right (by linarith)

lemma uB_of_le (M : Model) {x : ℝ} (hx : M.s * x ≤ M.v) : M.uB x = M.v - M.s * x := by
  unfold Model.uB; exact max_eq_left (by linarith)

lemma uB_of_ge (M : Model) {x : ℝ} (hx : M.v ≤ M.s * x) : M.uB x = 0 := by
  unfold Model.uB; exact max_eq_right (by linarith)

lemma uA_nonneg (M : Model) (x : ℝ) : 0 ≤ M.uA x := by unfold Model.uA; exact le_max_right _ _
lemma uB_nonneg (M : Model) (x : ℝ) : 0 ≤ M.uB x := by unfold Model.uB; exact le_max_right _ _

lemma uA_cont (M : Model) : Continuous M.uA := by unfold Model.uA; fun_prop
lemma uB_cont (M : Model) : Continuous M.uB := by unfold Model.uB; fun_prop

lemma rev1 (M : Model) {w x : ℝ} (h1 : w ≤ M.uB x) (h2 : M.uB x ≤ M.uA x) :
    M.revPP w x = w + M.uA x - M.uB x := by
  unfold Model.revPP
  rw [if_neg (by linarith), if_neg (by linarith), abs_of_nonneg (by linarith)]
  ring

lemma rev2 (M : Model) {w x : ℝ} (h1 : w ≤ M.uA x) (h2 : M.uA x ≤ M.uB x) :
    M.revPP w x = w + M.uB x - M.uA x := by
  unfold Model.revPP
  rw [if_neg (by linarith), if_neg (by linarith), abs_of_nonpos (by linarith)]
  ring

lemma rev3 (M : Model) {w x : ℝ} (h1 : w ≤ M.uB x) (h2 : M.uA x < w ∨ (M.uA x = 0 ∧ w = 0)) :
    M.revPP w x = M.uB x := by
  unfold Model.revPP
  rw [if_neg (by linarith)]
  rcases h2 with h2 | ⟨h2, h3⟩
  · rw [if_pos h2]
  · rw [if_neg (by linarith), h2, h3, abs_of_nonpos (by linarith [uB_nonneg M x])]
    ring

lemma rev4 (M : Model) {w x : ℝ} (h2 : M.uB x < w ∨ (M.uB x = 0 ∧ w = 0)) :
    M.revPP w x = M.uA x := by
  unfold Model.revPP
  rcases h2 with h2 | ⟨h2, h3⟩
  · rw [if_pos h2]
  · rw [if_neg (by linarith), if_neg (by linarith [uA_nonneg M x]), h2, h3,
      abs_of_nonneg (by linarith [uA_nonneg M x])]
    ring

lemma revPP_meas (M : Model) (w : ℝ) : Measurable (M.revPP w) := by
  have hA : Measurable M.uA := (uA_cont M).measurable
  have hB : Measurable M.uB := (uB_cont M).measurable
  unfold Model.revPP
  refine Measurable.ite (measurableSet_lt hB measurable_const) hA
    (Measurable.ite (measurableSet_lt hA measurable_const) hB ?_)
  exact measurable_const.add ((hA.sub hB).abs)

lemma revPP_bound (M : Model) (w x : ℝ) : |M.revPP w x| ≤ |w| + M.uA x + M.uB x := by
  have hA := uA_nonneg M x
  have hB := uB_nonneg M x
  unfold Model.revPP
  split_ifs
  · rw [abs_of_nonneg hA]; linarith [abs_nonneg w]
  · rw [abs_of_nonneg hB]; linarith [abs_nonneg w]
  · have h1 := abs_add_le w (|M.uA x - M.uB x|)
    rw [abs_abs] at h1
    have h2 := abs_sub (M.uA x) (M.uB x)
    rw [abs_of_nonneg hA, abs_of_nonneg hB] at h2
    linarith

lemma revPP_int (M : Model) (w a b : ℝ) : IntervalIntegrable (M.revPP w) MeasureTheory.volume a b := by
  have hg : IntervalIntegrable (fun x => |w| + M.uA x + M.uB x) MeasureTheory.volume a b := by
    apply Continuous.intervalIntegrable
    have := uA_cont M; have := uB_cont M
    fun_prop
  refine hg.mono_fun' (revPP_meas M w).aestronglyMeasurable ?_
  refine Filter.Eventually.of_forall (fun x => ?_)
  simpa [Real.norm_eq_abs] using revPP_bound M w x

lemma uA_int (M : Model) (a b : ℝ) : IntervalIntegrable M.uA MeasureTheory.volume a b :=
  (uA_cont M).intervalIntegrable a b

/-- Tail of the direct-channel value when the lower limit is at least `1`. -/
lemma tail_ge (M : Model) {p X : ℝ} (hp : 1 ≤ p) (hpX : p ≤ X) : ∫ x in p..X, M.uA x = 0 := by
  have : ∫ x in p..X, M.uA x = ∫ x in p..X, (0:ℝ) := by
    apply intervalIntegral.integral_congr
    intro x hx
    rw [Set.uIcc_of_le hpX] at hx
    exact uA_of_ge M (by linarith [hx.1])
  rw [this]; simp

lemma tail_le (M : Model) {p X : ℝ} (hp : p ≤ 1) (hX : 1 ≤ X) :
    ∫ x in p..X, M.uA x = (1 - p) ^ 2 / 2 := by
  rw [← intervalIntegral.integral_add_adjacent_intervals (uA_int M p 1) (uA_int M 1 X),
    tail_ge M le_rfl hX]
  have : ∫ x in p..1, M.uA x = ∫ x in p..1, (1 - 1 * x) := by
    apply intervalIntegral.integral_congr
    intro x hx
    rw [Set.uIcc_of_le hp] at hx
    rw [uA_of_le M hx.2]; ring
  rw [this, EF_lin]; ring

lemma monoP_eq (M : Model) (hM : M.Standing) : M.monoP = 1 / 2 := by
  have h1 : 1 ≤ M.v / M.s := by rw [le_div_iff₀ hM.s_pos]; linarith [hM.s_lt_v]
  unfold Model.monoP
  rw [tail_le M (by norm_num) (h1.trans hM.X_large)]
  norm_num

/-- Decomposition of PP industry profit for `0 ≤ w ≤ uhat`. -/
lemma indPP_split (M : Model) (hM : M.Standing) {w : ℝ} (hw0 : 0 ≤ w)
    (hwu : w * (1 - M.s) ≤ M.v - M.s) :
    M.indPP w =
      (∫ x in (0:ℝ)..M.xhat, ((w + (1 - M.v)) - (1 - M.s) * x)) +
      (∫ x in M.xhat..(1 - w), ((w + M.v - 1) - (M.s - 1) * x)) +
      (∫ x in (1 - w)..((M.v - w) / M.s), (M.v - M.s * x)) +
      (∫ x in ((M.v - w) / M.s)..M.X, M.uA x) := by
  obtain ⟨hs, hsv, hv1, hX⟩ := hM
  have h1s : 0 < 1 - M.s := by linarith
  have hxh : (1 - M.s) * M.xhat = 1 - M.v := by unfold Model.xhat; field_simp
  have hxh0 : 0 ≤ M.xhat := by unfold Model.xhat; apply div_nonneg <;> linarith
  have hxa : M.xhat ≤ 1 - w := by
    by_contra h; push Not at h
    have := mul_lt_mul_of_pos_left h h1s
    nlinarith
  have hsb : M.s * ((M.v - w) / M.s) = M.v - w := by field_simp
  have hab : 1 - w ≤ (M.v - w) / M.s := by
    rw [le_div_iff₀ hs]; nlinarith
  have hsX : M.v ≤ M.s * M.X := by
    have := (div_le_iff₀' hs).mp hX; linarith
  have hbX : (M.v - w) / M.s ≤ M.X := by
    rw [div_le_iff₀' hs]; linarith
  have hI := revPP_int M w
  unfold Model.indPP
  rw [← intervalIntegral.integral_add_adjacent_intervals (hI 0 M.xhat) (hI M.xhat _),
    ← intervalIntegral.integral_add_adjacent_intervals (hI M.xhat (1 - w)) (hI (1 - w) _),
    ← intervalIntegral.integral_add_adjacent_intervals (hI (1 - w) ((M.v - w) / M.s))
      (hI ((M.v - w) / M.s) M.X)]
  have e1 : ∫ x in (0:ℝ)..M.xhat, M.revPP w x =
      ∫ x in (0:ℝ)..M.xhat, ((w + (1 - M.v)) - (1 - M.s) * x) := by
    apply intervalIntegral.integral_congr_ae
    refine Filter.Eventually.of_forall (fun x hx => ?_)
    rw [Set.uIoc_of_le hxh0] at hx
    obtain ⟨hx1, hx2⟩ := hx
    have hx1' : x ≤ 1 := by linarith
    have hA := uA_of_le M hx1'
    have hB := uB_of_le M (show M.s * x ≤ M.v by nlinarith)
    have hxx : (1 - M.s) * x ≤ 1 - M.v := by nlinarith
    rw [rev1 M (by rw [hB]; nlinarith) (by rw [hA, hB]; nlinarith), hA, hB]
    ring
  have e2 : ∫ x in M.xhat..(1 - w), M.revPP w x =
      ∫ x in M.xhat..(1 - w), ((w + M.v - 1) - (M.s - 1) * x) := by
    apply intervalIntegral.integral_congr_ae
    refine Filter.Eventually.of_forall (fun x hx => ?_)
    rw [Set.uIoc_of_le hxa] at hx
    obtain ⟨hx1, hx2⟩ := hx
    have hx1' : x ≤ 1 := by linarith
    have hA := uA_of_le M hx1'
    have hB := uB_of_le M (show M.s * x ≤ M.v by nlinarith)
    have hxx : 1 - M.v ≤ (1 - M.s) * x := by nlinarith
    rw [rev2 M (by rw [hA]; linarith) (by rw [hA, hB]; nlinarith), hA, hB]
    ring
  have e3 : ∫ x in (1 - w)..((M.v - w) / M.s), M.revPP w x =
      ∫ x in (1 - w)..((M.v - w) / M.s), (M.v - M.s * x) := by
    apply intervalIntegral.integral_congr_ae
    refine Filter.Eventually.of_forall (fun x hx => ?_)
    rw [Set.uIoc_of_le hab] at hx
    obtain ⟨hx1, hx2⟩ := hx
    have hsx : M.s * x ≤ M.v - w := by
      have := mul_le_mul_of_nonneg_left hx2 hs.le; linarith
    have hB := uB_of_le M (show M.s * x ≤ M.v by linarith)
    have hA' : M.uA x < w ∨ (M.uA x = 0 ∧ w = 0) := by
      by_cases hx1' : x ≤ 1
      · left; rw [uA_of_le M hx1']; linarith
      · rw [uA_of_ge M (by linarith)]
        rcases lt_or_eq_of_le hw0 with h | h
        · left; exact h
        · right; exact ⟨rfl, h.symm⟩
    rw [rev3 M (by rw [hB]; linarith) hA', hB]
  have e4 : ∫ x in ((M.v - w) / M.s)..M.X, M.revPP w x =
      ∫ x in ((M.v - w) / M.s)..M.X, M.uA x := by
    apply intervalIntegral.integral_congr_ae
    refine Filter.Eventually.of_forall (fun x hx => ?_)
    rw [Set.uIoc_of_le hbX] at hx
    obtain ⟨hx1, hx2⟩ := hx
    have hsx : M.v - w < M.s * x := by
      have := mul_lt_mul_of_pos_left hx1 hs; linarith
    apply rev4
    by_cases hc : M.s * x ≤ M.v
    · left; rw [uB_of_le M hc]; linarith
    · push Not at hc
      rw [uB_of_ge M hc.le]
      rcases lt_or_eq_of_le hw0 with h | h
      · left; exact h
      · right; exact ⟨rfl, h.symm⟩
  rw [e1, e2, e3, e4]
  ring

/-- For `w ≥ uhat`, PP industry profit never exceeds the mono profit. -/
lemma indPP_le_high (M : Model) (hM : M.Standing) {w : ℝ}
    (hwu : M.v - M.s ≤ w * (1 - M.s)) : M.indPP w ≤ M.monoP := by
  obtain ⟨hs, hsv, hv1, hX⟩ := hM
  have h1s : 0 < 1 - M.s := by linarith
  have hX0 : 0 ≤ M.X := by
    have : 0 ≤ M.v / M.s := div_nonneg (by linarith) hs.le
    linarith
  unfold Model.indPP Model.monoP
  apply intervalIntegral.integral_mono_on hX0 (revPP_int M w 0 M.X) (uA_int M 0 M.X)
  intro x _
  -- key: if `uB x ≥ w` then `uB x ≤ uA x`
  have key : w ≤ M.uB x → M.uB x ≤ M.uA x := by
    intro h
    have hwpos : 0 < w := by
      have : 0 < w * (1 - M.s) := by linarith
      exact pos_of_mul_pos_left this h1s.le
    by_cases hc : M.s * x ≤ M.v
    · rw [uB_of_le M hc] at h ⊢
      have h2 : M.v - M.s ≤ (1 - M.s) * (M.v - M.s * x) := by nlinarith
      have h3 : (1 - M.s) * x ≤ 1 - M.v := by nlinarith
      have : 1 - x ≤ M.uA x := le_max_left _ _
      nlinarith
    · push Not at hc
      rw [uB_of_ge M hc.le] at h; linarith
  have hA := uA_nonneg M x
  have hB := uB_nonneg M x
  unfold Model.revPP
  split_ifs with h1 h2
  · exact le_rfl
  · exact key (not_lt.mp h1)
  · have := key (not_lt.mp h1)
    rw [abs_of_nonneg (by linarith)]
    linarith [not_lt.mp h1]

/-- The gain polynomial in the region `v - s < w < uhat` is nonpositive when `v ≤ ṽ(s)`. -/
lemma case2_ineq (s v w : ℝ) (hs : 0 < s) (hs1 : s < 1) (hv : s < v) (hv1 : v < 1)
    (hw1 : v - s < w) (hw2 : w * (1 - s) < v - s)
    (hN : (1 + s) ^ 2 * v ^ 2 - 4 * s * (1 + s) * v + s ^ 2 * (s + 3) ≤ 0) :
    s^3*w^2 - 2*s^3*w + s^3 + s^2*v^2 - 2*s^2*v + s^2 + 2*s*v*w - 2*s*v - 2*s*w^2 + 2*s*w
      + v^2 - 2*v*w + w^2 ≤ 0 := by
  set y := w - (v - s) with hy
  have hw : w = v - s + y := by rw [hy]; ring
  have hy0 : 0 < y := by rw [hy]; linarith
  set Y := s * (v - s) / (1 - s) with hYdef
  have h1s : 0 < 1 - s := by linarith
  have hYm : Y * (1 - s) = s * (v - s) := by rw [hYdef]; field_simp
  have hyY : y < Y := by
    by_contra h; push Not at h
    have := mul_le_mul_of_nonneg_right h h1s.le
    nlinarith
  set P2 := s ^ 3 - 2 * s + 1
  set P1 := -2*s^4 + 2*s^3*v - 2*s^3 + 4*s^2 - 2*s*v
  set P0 := s^5 - 2*s^4*v + 2*s^4 + s^3*v^2 - 2*s^3*v - s^3 + s^2*v^2
  have hP : s^3*w^2 - 2*s^3*w + s^3 + s^2*v^2 - 2*s^2*v + s^2 + 2*s*v*w - 2*s*v - 2*s*w^2
      + 2*s*w + v^2 - 2*v*w + w^2 = P2 * y ^ 2 + P1 * y + P0 := by
    rw [hw]; ring
  rw [hP]
  have hPY : P2 * Y ^ 2 + P1 * Y + P0 = -(s ^ 3 * (1 - v) ^ 2) / (1 - s) := by
    rw [hYdef]; field_simp; ring
  have hPYneg : P2 * Y ^ 2 + P1 * Y + P0 < 0 := by
    rw [hPY]; apply div_neg_of_neg_of_pos _ h1s
    have : 0 < s ^ 3 * (1 - v) ^ 2 := by positivity
    linarith
  have hdP : P1 + 2 * P2 * Y = 2 * s ^ 2 * (1 - v) := by
    rw [hYdef]; field_simp; ring
  by_cases hP2 : P2 ≤ 0
  · have hid : P2 * y ^ 2 + P1 * y + P0 - (P2 * Y ^ 2 + P1 * Y + P0)
        = (y - Y) * (2 * s ^ 2 * (1 - v) + P2 * (y - Y)) := by
      rw [← hdP]; ring
    have h3 : 0 < 2 * s ^ 2 * (1 - v) + P2 * (y - Y) := by
      have : 0 ≤ P2 * (y - Y) := mul_nonneg_of_nonpos_of_nonpos hP2 (by linarith)
      have : 0 < 2 * s ^ 2 * (1 - v) := by
        have : 0 < 1 - v := by linarith
        positivity
      linarith
    have : (y - Y) * (2 * s ^ 2 * (1 - v) + P2 * (y - Y)) < 0 :=
      mul_neg_of_neg_of_pos (by linarith) h3
    linarith
  · push Not at hP2
    have hP0 : P0 ≤ 0 := by
      have hid : P0 * (1 + s) = s * ((1 + s) ^ 2 * v ^ 2 - 4 * s * (1 + s) * v + s ^ 2 * (s + 3)
          - (1 - s) * ((1 + s) * v - s * (2 + s)) ^ 2) := by ring
      have : P0 * (1 + s) ≤ 0 := by
        rw [hid]
        apply mul_nonpos_of_nonneg_of_nonpos hs.le
        nlinarith [mul_nonneg h1s.le (sq_nonneg ((1 + s) * v - s * (2 + s)))]
      nlinarith
    have hid : Y * (P2 * y ^ 2 + P1 * y + P0)
        = (Y - y) * P0 + y * (P2 * Y ^ 2 + P1 * Y + P0) - P2 * Y * y * (Y - y) := by ring
    have hYpos : 0 < Y := by linarith
    have t1 : (Y - y) * P0 ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (by linarith) hP0
    have t2 : y * (P2 * Y ^ 2 + P1 * Y + P0) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos hy0.le hPYneg.le
    have t3 : 0 ≤ P2 * Y * y * (Y - y) := by
      have := mul_pos (mul_pos hP2 hYpos) hy0
      exact mul_nonneg this.le (by linarith)
    have : Y * (P2 * y ^ 2 + P1 * y + P0) ≤ 0 := by rw [hid]; linarith
    by_contra hc; push Not at hc
    have := mul_pos hYpos hc
    linarith

end PPDAPPCutAux

open PPDAPPCutAux in
theorem solution (M : Model) (hM : M.Standing) :
    M.DualPP ↔ Model.vTilde M.s < M.v := by
  have hs := hM.s_pos
  have hsv := hM.s_lt_v
  have hv1 := hM.v_lt_one
  have hX := hM.X_large
  have h1s : 0 < 1 - M.s := by linarith
  have h1v : 1 ≤ M.v / M.s := by rw [le_div_iff₀ hs]; linarith
  have hX1 : 1 ≤ M.X := h1v.trans hX
  set r := Real.sqrt (1 - M.s) with hr
  have hr2 : r ^ 2 = 1 - M.s := Real.sq_sqrt h1s.le
  have hr0 : 0 < r := Real.sqrt_pos.mpr h1s
  have hr1 : r < 1 := by nlinarith
  have hvt : Model.vTilde M.s < M.v ↔ M.s * (2 + r) < M.v * (1 + M.s) := by
    unfold Model.vTilde
    rw [div_lt_iff₀ (by linarith)]
  unfold Model.DualPP
  rw [monoP_eq M hM, hvt]
  set N := (1 + M.s) ^ 2 * M.v ^ 2 - 4 * M.s * (1 + M.s) * M.v + M.s ^ 2 * (M.s + 3) with hN
  have hNf : N = ((1 + M.s) * M.v - 2 * M.s - M.s * r) * ((1 + M.s) * M.v - 2 * M.s + M.s * r) := by
    rw [hN]; nlinarith [hr2]
  -- closed form of the gain in the region `0 ≤ w ≤ v - s`
  have gain1 : ∀ w, 0 ≤ w → w ≤ M.v - M.s →
      M.indPP w - 1 / 2 = (N - (1 - M.s) * ((1 + M.s) * w - M.s) ^ 2)
        / (2 * M.s * (1 - M.s) * (1 + M.s)) := by
    intro w hw0 hw1
    have hwu : w * (1 - M.s) ≤ M.v - M.s := by nlinarith
    have hb1 : 1 ≤ (M.v - w) / M.s := by rw [le_div_iff₀ hs]; linarith
    have hbX : (M.v - w) / M.s ≤ M.X := by
      have : (M.v - w) / M.s ≤ M.v / M.s := by
        apply div_le_div_of_nonneg_right (by linarith) hs.le
      linarith
    rw [indPP_split M hM hw0 hwu, tail_ge M hb1 hbX, EF_lin, EF_lin, EF_lin]
    unfold Model.xhat
    rw [hN]
    field_simp
    ring
  constructor
  · rintro ⟨w, hw0, hgain⟩
    by_contra hcon
    push Not at hcon
    have hNle : N ≤ 0 := by
      rw [hNf]
      apply mul_nonpos_of_nonpos_of_nonneg
      · nlinarith
      · nlinarith [mul_pos hs hr0, mul_pos hr0 (by linarith : (0:ℝ) < 1 - r)]
    rcases le_or_gt (M.v - M.s) (w * (1 - M.s)) with hhi | hlo
    · have := indPP_le_high M hM hhi
      rw [monoP_eq M hM] at this
      linarith
    · rcases le_or_gt w (M.v - M.s) with hw1 | hw1
      · have hg := gain1 w hw0 hw1
        have : (N - (1 - M.s) * ((1 + M.s) * w - M.s) ^ 2)
            / (2 * M.s * (1 - M.s) * (1 + M.s)) ≤ 0 := by
          apply div_nonpos_of_nonpos_of_nonneg
          · nlinarith [mul_nonneg h1s.le (sq_nonneg ((1 + M.s) * w - M.s))]
          · have := mul_pos (mul_pos hs h1s) (by linarith : (0:ℝ) < 1 + M.s)
            linarith
        linarith
      · -- region `v - s < w < uhat`
        have hb1 : (M.v - w) / M.s ≤ 1 := by rw [div_le_iff₀ hs]; linarith
        have hineq := case2_ineq M.s M.v w hs (by linarith) hsv hv1 hw1 hlo hNle
        have hval : M.indPP w - 1 / 2 =
            (M.s^3*w^2 - 2*M.s^3*w + M.s^3 + M.s^2*M.v^2 - 2*M.s^2*M.v + M.s^2 + 2*M.s*M.v*w
              - 2*M.s*M.v - 2*M.s*w^2 + 2*M.s*w + M.v^2 - 2*M.v*w + w^2)
              / (2 * M.s ^ 2 * (1 - M.s)) := by
          rw [indPP_split M hM hw0 hlo.le, tail_le M hb1 hX1, EF_lin, EF_lin, EF_lin]
          unfold Model.xhat
          field_simp
          ring
        have : (M.s^3*w^2 - 2*M.s^3*w + M.s^3 + M.s^2*M.v^2 - 2*M.s^2*M.v + M.s^2 + 2*M.s*M.v*w
              - 2*M.s*M.v - 2*M.s*w^2 + 2*M.s*w + M.v^2 - 2*M.v*w + w^2)
              / (2 * M.s ^ 2 * (1 - M.s)) ≤ 0 :=
          div_nonpos_of_nonpos_of_nonneg hineq (by positivity)
        linarith
  · intro hcon
    have hrs : M.s < r := by
      have : M.s * (2 + r) < 1 + M.s := by nlinarith
      nlinarith
    set w := M.s / (1 + M.s) with hwdef
    have hw0 : 0 ≤ w := by positivity
    have hw1 : w ≤ M.v - M.s := by
      rw [hwdef, div_le_iff₀ (by linarith)]
      nlinarith
    have hNpos : 0 < N := by
      rw [hNf]
      apply mul_pos
      · nlinarith
      · nlinarith [mul_pos hs hr0]
    refine ⟨w, hw0, ?_⟩
    have hg := gain1 w hw0 hw1
    have hz : (1 + M.s) * w - M.s = 0 := by rw [hwdef]; field_simp; ring
    rw [hz] at hg
    have : 0 < (N - (1 - M.s) * 0 ^ 2) / (2 * M.s * (1 - M.s) * (1 + M.s)) := by
      apply div_pos (by simpa using hNpos)
      have := mul_pos (mul_pos hs h1s) (by linarith : (0:ℝ) < 1 + M.s)
      linarith
    linarith
