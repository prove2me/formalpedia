-- Prove2me | solution 1 for ReflNewton.FirstOrder.theorem_8
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-28T21:16:50.27011+00:00
-- url     : https://prove2.me/submissions/b93b87ec-9b97-4383-865d-e69ee26663af

import Mathlib
import Definitions.Def_LewisTorczon_BoundPS_Box
import Definitions.Def_ReflNewton_FirstOrder_Setting

open Filter Topology

set_option autoImplicit false

namespace RN8

open ReflNewton.FirstOrder

lemma abs_coord_le {n : ℕ} (w : E n) (i : Fin n) : |w i| ≤ ‖w‖ := by
  have := PiLp.norm_apply_le w i
  simpa [Real.norm_eq_abs] using this

lemma norm_le_of_coord {n : ℕ} (w : E n) (B : ℝ) (hB : 0 ≤ B) (h : ∀ i, |w i| ≤ B) :
    ‖w‖ ≤ n * B := by
  have h1 : ‖w‖ ^ 2 ≤ (n * B) ^ 2 := by
    rw [PiLp.norm_sq_eq_of_L2]
    calc ∑ i, ‖w i‖ ^ 2 ≤ ∑ _i : Fin n, B ^ 2 := by
          apply Finset.sum_le_sum; intro i _
          rw [Real.norm_eq_abs]
          exact pow_le_pow_left₀ (abs_nonneg _) (h i) 2
      _ = n * B ^ 2 := by simp
      _ ≤ (n * B) ^ 2 := by
          rw [mul_pow]
          have : (n:ℝ) ≤ (n:ℝ) ^ 2 := by
            rcases Nat.eq_zero_or_pos n with h0 | h0
            · simp [h0]
            · have : (1:ℝ) ≤ n := by exact_mod_cast h0
              nlinarith
          nlinarith [sq_nonneg B]
  have : 0 ≤ (n:ℝ) * B := mul_nonneg (Nat.cast_nonneg n) hB
  nlinarith [norm_nonneg w]

lemma norm_le_norm_of_coord {n : ℕ} (a b : E n) (h : ∀ i, |a i| ≤ |b i|) : ‖a‖ ≤ ‖b‖ := by
  have h1 : ‖a‖ ^ 2 ≤ ‖b‖ ^ 2 := by
    rw [PiLp.norm_sq_eq_of_L2, PiLp.norm_sq_eq_of_L2]
    apply Finset.sum_le_sum; intro i _
    simp only [Real.norm_eq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _) (h i) 2
  nlinarith [norm_nonneg a, norm_nonneg b]

lemma ereal_toReal_le {a : EReal} {c : ℝ} (ha : a ≠ ⊥) (h : a ≤ (c : EReal)) : a.toReal ≤ c := by
  have ha' : a ≠ ⊤ := ne_top_of_le_ne_top (EReal.coe_ne_top c) h
  rw [← EReal.coe_toReal ha' ha] at h
  exact EReal.coe_le_coe_iff.mp h

lemma ereal_le_toReal {b : EReal} {c : ℝ} (hb : b ≠ ⊤) (h : (c : EReal) ≤ b) : c ≤ b.toReal := by
  have hb' : b ≠ ⊥ := ne_bot_of_le_ne_bot (EReal.coe_ne_bot c) h
  rw [← EReal.coe_toReal hb hb'] at h
  exact EReal.coe_le_coe_iff.mp h

lemma ereal_toReal_lt {a : EReal} {c : ℝ} (ha : a ≠ ⊥) (h : a < (c : EReal)) : a.toReal < c := by
  have ha' : a ≠ ⊤ := ne_top_of_le_ne_top (EReal.coe_ne_top c) h.le
  rw [← EReal.coe_toReal ha' ha] at h
  exact EReal.coe_lt_coe_iff.mp h

lemma ereal_lt_toReal {b : EReal} {c : ℝ} (hb : b ≠ ⊤) (h : (c : EReal) < b) : c < b.toReal := by
  have hb' : b ≠ ⊥ := ne_bot_of_le_ne_bot (EReal.coe_ne_bot c) h.le
  rw [← EReal.coe_toReal hb hb'] at h
  exact EReal.coe_lt_coe_iff.mp h

lemma tri_le (P t s : ℝ) (hP : 0 < P) (ht : 0 ≤ t) (hs0 : 0 ≤ s) (hs1 : s ≤ P / 2) :
    |min (P * Int.fract (t / P)) (P - P * Int.fract (t / P)) - s| ≤ |t - s| := by
  have hf0 := Int.fract_nonneg (t / P)
  have hf1 := Int.fract_lt_one (t / P)
  have hPt : P * (t / P) = t := by field_simp
  have hfe : P * Int.fract (t / P) = t - P * (⌊t / P⌋ : ℝ) := by
    unfold Int.fract; rw [mul_sub, hPt]
  have hm0 : (0:ℤ) ≤ ⌊t / P⌋ := Int.floor_nonneg.mpr (div_nonneg ht hP.le)
  have hw0 : 0 ≤ P * Int.fract (t / P) := mul_nonneg hP.le hf0
  have hw1 : P * Int.fract (t / P) < P := by nlinarith
  rcases (show ⌊t / P⌋ = 0 ∨ 1 ≤ ⌊t / P⌋ by omega) with h0 | h1
  · rw [h0] at hfe
    simp only [Int.cast_zero, mul_zero, sub_zero] at hfe
    rw [hfe]
    rw [hfe] at hw1
    rcases le_total t (P - t) with h | h
    · rw [min_eq_left h]
    · rw [min_eq_right h, abs_of_nonneg (by linarith : 0 ≤ t - s), abs_le]
      constructor <;> linarith
  · have h1' : (1:ℝ) ≤ ⌊t / P⌋ := by exact_mod_cast h1
    have htP : P ≤ t := by nlinarith
    rw [abs_of_nonneg (by linarith : 0 ≤ t - s), abs_le]
    have hmin0 : 0 ≤ min (P * Int.fract (t / P)) (P - P * Int.fract (t / P)) :=
      le_min hw0 (by linarith)
    have hmin1 : min (P * Int.fract (t / P)) (P - P * Int.fract (t / P)) ≤ P / 2 := by
      rcases le_total (P * Int.fract (t / P)) (P / 2) with h | h
      · exact (min_le_left _ _).trans h
      · exact (min_le_right _ _).trans (by linarith)
    constructor <;> linarith

lemma reflectCoord_le (a b : EReal) (c y : ℝ) (ha : a ≤ (c : EReal)) (hb : (c : EReal) ≤ b) :
    |reflectCoord a b y - c| ≤ |y - c| := by
  unfold reflectCoord
  by_cases ha' : a = ⊥
  · rw [if_pos ha']
    by_cases hb' : b = ⊤
    · rw [if_pos hb']
    · rw [if_neg hb']
      have hbc : c ≤ b.toReal := ereal_le_toReal hb' hb
      split_ifs with hy
      · exact le_rfl
      · rw [not_le] at hy
        rw [abs_of_nonneg (by linarith : 0 ≤ y - c), abs_le]
        constructor <;> linarith
  · rw [if_neg ha']
    have hac : a.toReal ≤ c := ereal_toReal_le ha' ha
    by_cases hb' : b = ⊤
    · rw [if_pos hb']
      split_ifs with hy
      · exact le_rfl
      · rw [not_le] at hy
        rw [abs_of_nonpos (by linarith : y - c ≤ 0), abs_le]
        constructor <;> linarith
    · rw [if_neg hb']
      have hbc : c ≤ b.toReal := ereal_le_toReal hb' hb
      simp only
      have key : |(y - a.toReal)| - (c - a.toReal) ≤ |y - c| ∧
          (c - a.toReal) - |(y - a.toReal)| ≤ |y - c| := by
        have h1 := abs_sub_abs_le_abs_sub (y - a.toReal) (c - a.toReal)
        have h2 := abs_sub_abs_le_abs_sub (c - a.toReal) (y - a.toReal)
        rw [abs_of_nonneg (by linarith : 0 ≤ c - a.toReal)] at h1 h2
        have e1 : y - a.toReal - (c - a.toReal) = y - c := by ring
        have e2 : c - a.toReal - (y - a.toReal) = -(y - c) := by ring
        rw [e1] at h1; rw [e2, abs_neg] at h2
        exact ⟨h1, h2⟩
      rcases eq_or_lt_of_le (show 0 ≤ 2 * (b.toReal - a.toReal) by linarith) with hP | hP
      · rw [← hP]
        have hab : a.toReal = c := by linarith
        simp only [zero_mul, sub_zero, min_self, zero_add, hab, sub_self, abs_zero]
        exact abs_nonneg _
      · have h := tri_le (2 * (b.toReal - a.toReal)) |y - a.toReal| (c - a.toReal) hP
          (abs_nonneg _) (by linarith) (by linarith)
        have e3 : min (2 * (b.toReal - a.toReal) * Int.fract (|y - a.toReal| / (2 * (b.toReal - a.toReal))))
            (2 * (b.toReal - a.toReal) -
              2 * (b.toReal - a.toReal) * Int.fract (|y - a.toReal| / (2 * (b.toReal - a.toReal))))
            + a.toReal - c =
            min (2 * (b.toReal - a.toReal) * Int.fract (|y - a.toReal| / (2 * (b.toReal - a.toReal))))
            (2 * (b.toReal - a.toReal) -
              2 * (b.toReal - a.toReal) * Int.fract (|y - a.toReal| / (2 * (b.toReal - a.toReal))))
            - (c - a.toReal) := by ring
        rw [e3]
        refine h.trans ?_
        rw [abs_le]; constructor <;> linarith [key.1, key.2]

lemma reflect_norm_le {n : ℕ} (l u : Fin n → EReal) (c y : E n)
    (hc : c ∈ LewisTorczon.BoundPS.box l u) : ‖reflect l u y - c‖ ≤ ‖y - c‖ := by
  apply norm_le_norm_of_coord
  intro i
  show |reflectCoord (l i) (u i) (y i) - c i| ≤ |y i - c i|
  exact reflectCoord_le _ _ _ _ (hc i).1 (hc i).2

lemma vCoord_abs_le (a b : EReal) (xi gi : ℝ) :
    |vCoord a b xi gi| ≤ 1 + |xi - a.toReal| + |xi - b.toReal| := by
  have h1 := abs_nonneg (xi - a.toReal)
  have h2 := abs_nonneg (xi - b.toReal)
  unfold vCoord
  split_ifs
  · rw [abs_neg, abs_one]; linarith
  · linarith
  · rw [abs_one]; linarith
  · linarith


lemma grad_C1 {n : ℕ} (f : E n → ℝ) (D : Set (E n)) (hDo : IsOpen D)
    (hf : ContDiffOn ℝ 2 f D) {y : E n} (hy : y ∈ D) : ContDiffAt ℝ 1 (gradient f) y := by
  have h1 : ContDiffAt ℝ 2 f y := hf.contDiffAt (hDo.mem_nhds hy)
  have h2 : ContDiffAt ℝ 1 (fderiv ℝ f) y := h1.fderiv_right (by norm_num)
  have : gradient f = fun x => (InnerProductSpace.toDual ℝ (E n)).symm (fderiv ℝ f x) := rfl
  rw [this]
  exact (InnerProductSpace.toDual ℝ (E n)).symm.contDiff.contDiffAt.comp y h2

lemma reflectCoord_id (a b : EReal) (y : ℝ) (ha : a ≤ (y : EReal)) (hb : (y : EReal) ≤ b) :
    reflectCoord a b y = y := by
  unfold reflectCoord
  by_cases ha' : a = ⊥
  · rw [if_pos ha']
    by_cases hb' : b = ⊤
    · rw [if_pos hb']
    · rw [if_neg hb', if_pos (ereal_le_toReal hb' hb)]
  · rw [if_neg ha']
    have hay : a.toReal ≤ y := ereal_toReal_le ha' ha
    by_cases hb' : b = ⊤
    · rw [if_pos hb', if_pos hay]
    · rw [if_neg hb']
      have hyb : y ≤ b.toReal := ereal_le_toReal hb' hb
      simp only
      rw [abs_of_nonneg (by linarith : 0 ≤ y - a.toReal)]
      rcases eq_or_lt_of_le (show 0 ≤ 2 * (b.toReal - a.toReal) by linarith) with hP | hP
      · rw [← hP]
        simp only [zero_mul, sub_zero, min_self, zero_add]
        linarith
      · have hq0 : 0 ≤ (y - a.toReal) / (2 * (b.toReal - a.toReal)) :=
          div_nonneg (by linarith) hP.le
        have hq1 : (y - a.toReal) / (2 * (b.toReal - a.toReal)) < 1 := by
          rw [div_lt_one hP]; linarith
        rw [Int.fract_eq_self.mpr ⟨hq0, hq1⟩]
        have e : 2 * (b.toReal - a.toReal) * ((y - a.toReal) / (2 * (b.toReal - a.toReal)))
            = y - a.toReal := by
          rw [mul_div_assoc']; exact mul_div_cancel_left₀ _ hP.ne'
        rw [e, min_eq_left (by linarith)]
        ring

lemma vCoord_ne_zero (a b : EReal) (xi gi : ℝ) (ha : a < (xi : EReal)) (hb : (xi : EReal) < b) :
    vCoord a b xi gi ≠ 0 := by
  unfold vCoord
  split_ifs with h1 h2 h3
  · norm_num
  · intro h; have := ereal_lt_toReal h2 hb; linarith
  · norm_num
  · intro h; have := ereal_toReal_lt h3 ha; linarith

lemma coord_key (a b : EReal) (xi si gi α B : ℝ) (ha : a < (xi : EReal)) (hb : (xi : EReal) < b)
    (hα : 0 ≤ α) (hB : 0 ≤ B) (hαB : α * B < 1) (hs : |si| ≤ B * |vCoord a b xi gi|) :
    gi * (reflectCoord a b (xi + α * si) - xi) ≤ gi * (α * si) := by
  have hR := reflectCoord_le a b xi (xi + α * si) ha.le hb.le
  have e : xi + α * si - xi = α * si := by ring
  rw [e] at hR
  have hbne : b ≠ ⊥ := (bot_le.trans_lt hb).ne'
  have hane : a ≠ ⊤ := (ha.trans_le le_top).ne
  rcases lt_or_ge gi 0 with hg | hg
  · have hv : vCoord a b xi gi = if b = ⊤ then -1 else xi - b.toReal := by
      unfold vCoord; rw [if_pos hg]
    suffices h : α * si ≤ reflectCoord a b (xi + α * si) - xi from
      mul_le_mul_of_nonpos_left h hg.le
    rcases le_or_gt si 0 with hs0 | hs0
    · have h0 : α * si ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hα hs0
      rw [abs_of_nonpos h0] at hR
      linarith [neg_abs_le (reflectCoord a b (xi + α * si) - xi)]
    · have hyb : ((xi + α * si : ℝ) : EReal) ≤ b := by
        by_cases hbt : b = ⊤
        · rw [hbt]; exact le_top
        · rw [hv, if_neg hbt] at hs
          have hxb := ereal_lt_toReal hbt hb
          rw [abs_of_neg (by linarith : xi - b.toReal < 0), abs_of_pos hs0] at hs
          have h1 : α * si ≤ α * (B * (-(xi - b.toReal))) := mul_le_mul_of_nonneg_left hs hα
          have h2 : α * (B * (-(xi - b.toReal))) < b.toReal - xi := by
            nlinarith [mul_pos (by linarith : 0 < b.toReal - xi) (by linarith : 0 < 1 - α * B)]
          have h3 : xi + α * si ≤ b.toReal := by linarith
          calc ((xi + α * si : ℝ) : EReal) ≤ (b.toReal : EReal) := EReal.coe_le_coe_iff.mpr h3
            _ = b := EReal.coe_toReal hbt hbne
      have hay : a ≤ ((xi + α * si : ℝ) : EReal) :=
        le_trans ha.le (EReal.coe_le_coe_iff.mpr (by nlinarith [mul_nonneg hα hs0.le]))
      rw [reflectCoord_id a b _ hay hyb]
      linarith
  · have hv : vCoord a b xi gi = if a = ⊥ then 1 else xi - a.toReal := by
      unfold vCoord; rw [if_neg (not_lt.mpr hg)]
    suffices h : reflectCoord a b (xi + α * si) - xi ≤ α * si from
      mul_le_mul_of_nonneg_left h hg
    rcases le_or_gt 0 si with hs0 | hs0
    · have h0 : 0 ≤ α * si := mul_nonneg hα hs0
      rw [abs_of_nonneg h0] at hR
      linarith [le_abs_self (reflectCoord a b (xi + α * si) - xi)]
    · have hay : a ≤ ((xi + α * si : ℝ) : EReal) := by
        by_cases hat : a = ⊥
        · rw [hat]; exact bot_le
        · rw [hv, if_neg hat] at hs
          have hxa := ereal_toReal_lt hat ha
          rw [abs_of_pos (by linarith : 0 < xi - a.toReal), abs_of_neg hs0] at hs
          have h1 : α * (-si) ≤ α * (B * (xi - a.toReal)) := mul_le_mul_of_nonneg_left hs hα
          have h2 : α * (B * (xi - a.toReal)) < xi - a.toReal := by
            nlinarith [mul_pos (by linarith : 0 < xi - a.toReal) (by linarith : 0 < 1 - α * B)]
          have h3 : a.toReal ≤ xi + α * si := by linarith
          calc a = (a.toReal : EReal) := (EReal.coe_toReal hane hat).symm
            _ ≤ ((xi + α * si : ℝ) : EReal) := EReal.coe_le_coe_iff.mpr h3
      have hyb : ((xi + α * si : ℝ) : EReal) ≤ b :=
        le_trans (EReal.coe_le_coe_iff.mpr (by nlinarith [mul_nonneg hα (neg_nonneg.mpr hs0.le)])) hb.le
      rw [reflectCoord_id a b _ hay hyb]
      linarith

lemma inner_le_zero_of_descent {n : ℕ} (l u : Fin n → EReal) (f : E n → ℝ) (x s : E n)
    (hx : x ∈ intBox l u) (hd : IsDescentDir l u f x s) (hdiff : DifferentiableAt ℝ f x) :
    inner ℝ (gradient f x) s ≤ 0 := by
  by_contra hpos
  push Not at hpos
  obtain ⟨ε, hε, hdesc⟩ := hd
  have hline : HasDerivAt (fun t : ℝ => x + t • s) s 0 := by
    simpa using ((hasDerivAt_id (0:ℝ)).smul_const s).const_add x
  have hφ : HasDerivAt (fun t : ℝ => f (x + t • s)) (inner ℝ (gradient f x) s) 0 := by
    have h1 : HasFDerivAt f (InnerProductSpace.toDual ℝ (E n) (gradient f x)) (x + (0:ℝ) • s) := by
      rw [zero_smul, add_zero]; exact hdiff.hasGradientAt.hasFDerivAt
    have h2 := h1.comp_hasDerivAt (0:ℝ) hline
    rw [InnerProductSpace.toDual_apply_apply] at h2
    exact h2
  have hslope := hφ.tendsto_slope_zero_right
  have ev1 : ∀ᶠ t in 𝓝[>] (0:ℝ), 0 < t⁻¹ • (f (x + (0 + t) • s) - f (x + (0:ℝ) • s)) :=
    hslope.eventually (lt_mem_nhds hpos)
  have ev2a : ∀ᶠ t in 𝓝[>] (0:ℝ), 0 < t := self_mem_nhdsWithin
  have ev2b : ∀ᶠ t in 𝓝[>] (0:ℝ), t < ε := nhdsWithin_le_nhds (gt_mem_nhds hε)
  have ev2 : ∀ᶠ t in 𝓝[>] (0:ℝ), 0 < t ∧ t < ε := ev2a.and ev2b
  have ev3 : ∀ᶠ t in 𝓝[>] (0:ℝ), ∀ i, l i ≤ (((x + t • s) i : ℝ) : EReal) ∧
      (((x + t • s) i : ℝ) : EReal) ≤ u i := by
    refine nhdsWithin_le_nhds ?_
    show ∀ᶠ t in 𝓝 (0:ℝ), ∀ i, l i ≤ (((x + t • s) i : ℝ) : EReal) ∧
      (((x + t • s) i : ℝ) : EReal) ≤ u i
    rw [Filter.eventually_all]
    intro i
    have hc : Continuous (fun t : ℝ => (((x + t • s) i : ℝ) : EReal)) := by
      apply continuous_coe_real_ereal.comp
      simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
      fun_prop
    have h0l : l i < (fun t : ℝ => (((x + t • s) i : ℝ) : EReal)) 0 := by simpa using (hx i).1
    have h0u : (fun t : ℝ => (((x + t • s) i : ℝ) : EReal)) 0 < u i := by simpa using (hx i).2
    have e1 := hc.continuousAt.eventually (lt_mem_nhds h0l)
    have e2 := hc.continuousAt.eventually (gt_mem_nhds h0u)
    filter_upwards [e1, e2] with t ht1 ht2
    exact ⟨ht1.le, ht2.le⟩
  obtain ⟨t, ht1, ⟨ht0, htε⟩, ht3⟩ := (ev1.and (ev2.and ev3)).exists
  have hrefl : reflect l u (x + t • s) = x + t • s := by
    apply PiLp.ext
    intro i
    exact reflectCoord_id _ _ _ (ht3 i).1 (ht3 i).2
  have hlt := hdesc t ht0 htε
  simp only [reflPath, hrefl, add_sub_cancel] at hlt
  simp only [zero_add, zero_smul, add_zero, smul_eq_mul] at ht1
  have : 0 < f (x + t • s) - f x := by
    by_contra hc; push Not at hc
    have : t⁻¹ * (f (x + t • s) - f x) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (inv_nonneg.mpr ht0.le) hc
    linarith
  linarith

lemma taylor_up {n : ℕ} (f : E n → ℝ) (D : Set (E n)) (hDo : IsOpen D)
    (hf : ContDiffOn ℝ 2 f D) (x z : E n) (M : ℝ) (hM : 0 ≤ M)
    (hball : Metric.closedBall x ‖z - x‖ ⊆ D)
    (hH : ∀ w ∈ Metric.closedBall x ‖z - x‖, ‖fderiv ℝ (gradient f) w‖ ≤ M) :
    f z - f x ≤ inner ℝ (gradient f x) (z - x) + M * ‖z - x‖ ^ 2 := by
  set r := ‖z - x‖ with hr
  have hzmem : z ∈ Metric.closedBall x r := by rw [Metric.mem_closedBall, dist_eq_norm]
  have hxmem : x ∈ Metric.closedBall x r := Metric.mem_closedBall_self (norm_nonneg _)
  have hder : ∀ y ∈ Metric.closedBall x r,
      HasFDerivWithinAt (gradient f) (fderiv ℝ (gradient f) y) (Metric.closedBall x r) y :=
    fun y hy => ((grad_C1 f D hDo hf (hball hy)).differentiableAt
      (by norm_num)).hasFDerivAt.hasFDerivWithinAt
  have hgrad : ∀ w ∈ Metric.closedBall x r, ‖gradient f w - gradient f x‖ ≤ M * ‖w - x‖ :=
    fun w hw => (convex_closedBall x r).norm_image_sub_le_of_norm_hasFDerivWithin_le hder hH
      hxmem hw
  have hdiff : ∀ w ∈ Metric.closedBall x r, DifferentiableAt ℝ f w := fun w hw =>
    (hf.contDiffAt (hDo.mem_nhds (hball hw))).differentiableAt (by norm_num)
  set L0 := InnerProductSpace.toDual ℝ (E n) (gradient f x) with hL0
  have hder2 : ∀ w ∈ Metric.closedBall x r, HasFDerivWithinAt (fun y => f y - L0 y)
      (InnerProductSpace.toDual ℝ (E n) (gradient f w) - L0) (Metric.closedBall x r) w := by
    intro w hw
    exact ((hdiff w hw).hasGradientAt.hasFDerivAt.sub L0.hasFDerivAt).hasFDerivWithinAt
  have hbd2 : ∀ w ∈ Metric.closedBall x r,
      ‖InnerProductSpace.toDual ℝ (E n) (gradient f w) - L0‖ ≤ M * r := by
    intro w hw
    rw [hL0, ← map_sub, LinearIsometryEquiv.norm_map]
    refine (hgrad w hw).trans (mul_le_mul_of_nonneg_left ?_ hM)
    rw [Metric.mem_closedBall, dist_eq_norm] at hw; exact hw
  have hmv := (convex_closedBall x r).norm_image_sub_le_of_norm_hasFDerivWithin_le hder2 hbd2
    hxmem hzmem
  have e : (f z - L0 z) - (f x - L0 x) = (f z - f x) - inner ℝ (gradient f x) (z - x) := by
    simp only [hL0, InnerProductSpace.toDual_apply_apply, inner_sub_right]; ring
  rw [e, Real.norm_eq_abs] at hmv
  have h1 := le_abs_self ((f z - f x) - inner ℝ (gradient f x) (z - x))
  have h2 : M * r * r = M * r ^ 2 := by ring
  linarith

lemma inner_coord {n : ℕ} (a b : E n) : inner ℝ a b = ∑ i, a i * b i := by
  rw [PiLp.inner_apply]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [real_inner_eq_re_inner]
  simp [mul_comm]

lemma arith_key (a t N S M mm σu fz fx : ℝ) (ha : 0 < a) (ht : 0 ≤ t) (hN0 : 0 ≤ N)
    (hNS : N ≤ S) (hM : 0 ≤ M) (hσ0 : 0 < σu) (hσ1 : σu < 1)
    (hmm1 : -(M * N ^ 2) ≤ mm)
    (h35 : fx + σu * (a * (-t) + 1 / 2 * a ^ 2 * mm) < fz)
    (htay : fz - fx ≤ a * (-t) + M * (a * N) ^ 2) :
    (1 - σu) * t ≤ 2 * M * S ^ 2 * a := by
  have h1 : (1 - σu) * (a * t) < M * a ^ 2 * N ^ 2 - σu / 2 * a ^ 2 * mm := by nlinarith
  have h2 : -(σu / 2 * a ^ 2 * mm) ≤ σu / 2 * a ^ 2 * (M * N ^ 2) := by
    have := mul_le_mul_of_nonneg_left hmm1 (by positivity : 0 ≤ σu / 2 * a ^ 2)
    linarith
  have hNS2 : N ^ 2 ≤ S ^ 2 := pow_le_pow_left₀ hN0 hNS 2
  have h3 : M * a ^ 2 * N ^ 2 ≤ M * a ^ 2 * S ^ 2 :=
    mul_le_mul_of_nonneg_left hNS2 (by positivity)
  have h4 : 0 ≤ M * a ^ 2 * S ^ 2 := by positivity
  have h5 : σu / 2 * a ^ 2 * (M * N ^ 2) ≤ M * a ^ 2 * S ^ 2 := by
    have : σu / 2 * a ^ 2 * (M * N ^ 2) = (σu / 2) * (M * a ^ 2 * N ^ 2) := by ring
    rw [this]
    have h6 : 0 ≤ M * a ^ 2 * N ^ 2 := by positivity
    nlinarith
  have h7 : a * ((1 - σu) * t) < a * (2 * M * S ^ 2 * a) := by nlinarith
  exact (lt_of_mul_lt_mul_left h7 ha.le).le

end RN8

open ReflNewton.FirstOrder Filter Topology in
theorem solution
    {n : ℕ} (l u : Fin n → EReal) (hl : ∀ i, l i ≠ ⊤) (hu : ∀ i, u i ≠ ⊥) (hlu : l ≤ u)
    (f : E n → ℝ) (D : Set (E n)) (hDo : IsOpen D)
    (hFD : LewisTorczon.BoundPS.box l u ⊆ D) (hf : ContDiffOn ℝ 2 f D)
    (σl σu ρ : ℝ) (hσl : 0 < σl) (hσlu : σl < σu) (hσu : σu < 1) (hρ : 0 < ρ)
    (x s : ℕ → E n) (α : ℕ → ℝ) (hrun : IsIRRun l u f σl σu ρ x s α)
    (hL : IsCompact (LewisTorczon.BoundPS.levelSet l u f (x 0)))
    (hcons : IsConsistent l u f x s)
    (hcc : IsConstraintCompatible l u f x s) :
    Tendsto (fun k => dSqG l u f (x k)) atTop (𝓝 0) ∧
      Tendsto (fun k => α k ^ 2 * min (hq f (x k) (s k)) 0) atTop (𝓝 0) := by
  classical
  obtain ⟨hx0, hstep⟩ := hrun
  set L := LewisTorczon.BoundPS.levelSet l u f (x 0) with hLdef
  have hint : ∀ k, x k ∈ intBox l u := by
    intro k
    cases k with
    | zero => exact hx0
    | succ k => rw [(hstep k).2.2.2.2.2]; exact (hstep k).2.2.1
  have hbox : ∀ y, y ∈ intBox l u → y ∈ LewisTorczon.BoundPS.box l u :=
    fun y hy i => ⟨(hy i).1.le, (hy i).2.le⟩
  have hdiffD : ∀ y ∈ D, DifferentiableAt ℝ f y := fun y hy =>
    (hf.contDiffAt (hDo.mem_nhds hy)).differentiableAt (by norm_num)
  have hgs : ∀ k, inner ℝ (gradient f (x k)) (s k) ≤ 0 := fun k =>
    RN8.inner_le_zero_of_descent l u f (x k) (s k) (hint k) (hstep k).1
      (hdiffD _ (hFD (hbox _ (hint k))))
  set P : ℕ → ℝ := fun k => α k * (-inner ℝ (gradient f (x k)) (s k)) with hPdef
  set Q : ℕ → ℝ := fun k => -(α k ^ 2 * min (hq f (x k) (s k)) 0) with hQdef
  have hP0 : ∀ k, 0 ≤ P k := fun k =>
    mul_nonneg (hstep k).2.1.le (neg_nonneg.mpr (hgs k))
  have hQ0 : ∀ k, 0 ≤ Q k := fun k =>
    neg_nonneg.mpr (mul_nonpos_of_nonneg_of_nonpos (sq_nonneg _) (min_le_right _ _))
  have hdec : ∀ k, f (x (k + 1)) + σl * (P k + 1 / 2 * Q k) < f (x k) := by
    intro k
    have h34 := (hstep k).2.2.2.1
    unfold cond34 at h34
    simp only [hPdef, hQdef]
    linarith
  have hanti : Antitone (fun k => f (x k)) := by
    refine antitone_nat_of_succ_le (fun k => ?_)
    have h1 := hdec k
    have h2 : 0 ≤ σl * (P k + 1 / 2 * Q k) :=
      mul_nonneg hσl.le (by linarith [hP0 k, hQ0 k])
    show f (x (k + 1)) ≤ f (x k)
    linarith
  have hxL : ∀ k, x k ∈ L := fun k => ⟨hbox _ (hint k), hanti (Nat.zero_le k)⟩
  have hLD : L ⊆ D := fun y hy => hFD hy.1
  obtain ⟨y0, -, hmin⟩ := hL.exists_isMinOn ⟨x 0, hxL 0⟩ (hf.continuousOn.mono hLD)
  have hconv : Tendsto (fun k => f (x k)) atTop (𝓝 (⨅ k, f (x k))) :=
    tendsto_atTop_ciInf hanti ⟨f y0, by rintro _ ⟨k, rfl⟩; exact hmin (hxL k)⟩
  have hΔ : Tendsto (fun k => f (x k) - f (x (k + 1))) atTop (𝓝 0) := by
    have := hconv.sub (hconv.comp (tendsto_add_atTop_nat 1))
    simpa [Function.comp_def] using this
  have hPt : Tendsto P atTop (𝓝 0) := by
    refine squeeze_zero hP0 (fun k => ?_) (by simpa using hΔ.div_const σl)
    rw [le_div_iff₀ hσl]
    have := hdec k; have := hQ0 k
    nlinarith
  have hQt : Tendsto Q atTop (𝓝 0) := by
    refine squeeze_zero hQ0 (fun k => ?_) (by simpa using (hΔ.const_mul 2).div_const σl)
    rw [le_div_iff₀ hσl]
    have := hdec k; have := hP0 k
    nlinarith
  refine ⟨?_, by simpa [hQdef] using hQt.neg⟩
  -- bounds on the level set
  obtain ⟨R, hR⟩ := hL.isBounded.exists_norm_le
  obtain ⟨W, hW⟩ := (Set.finite_range (fun i => |(l i).toReal| + |(u i).toReal|)).bddAbove
  have hWi : ∀ i, |(l i).toReal| + |(u i).toReal| ≤ W := fun i => hW ⟨i, rfl⟩
  have hR0 : 0 ≤ R := (norm_nonneg _).trans (hR _ (hxL 0))
  set V := 1 + 2 * R + |W| with hV
  have hV0 : 0 ≤ V := by have := abs_nonneg W; linarith
  have hvb : ∀ k i, |vVec l u f (x k) i| ≤ V := by
    intro k i
    have h1 := RN8.vCoord_abs_le (l i) (u i) (x k i) (gradient f (x k) i)
    have h2 := RN8.abs_coord_le (x k) i
    have h3 := hR _ (hxL k)
    have h4 := hWi i
    have h5 := abs_sub (x k i) (l i).toReal
    have h6 := abs_sub (x k i) (u i).toReal
    have h7 := le_abs_self W
    show |vCoord (l i) (u i) (x k i) (gradient f (x k) i)| ≤ V
    linarith
  obtain ⟨B0, hB0⟩ := hcc.exists_norm_le
  set B := |B0| + 1 with hBdef
  have hB : 0 < B := by have := abs_nonneg B0; linarith
  have hsv : ∀ k i, |s k i| ≤ B * |vVec l u f (x k) i| := by
    intro k i
    have hvpos : 0 < |vVec l u f (x k) i| :=
      abs_pos.mpr (RN8.vCoord_ne_zero _ _ _ _ (hint k i).1 (hint k i).2)
    have h1 : abs (s k i / |vVec l u f (x k) i|) ≤ B0 :=
      (RN8.abs_coord_le (dInvSq l u f (x k) (s k)) i).trans (hB0 _ ⟨k, rfl⟩)
    rw [abs_div, abs_abs, div_le_iff₀ hvpos] at h1
    have := le_abs_self B0
    nlinarith
  set S := (n : ℝ) * (B * V) with hSdef
  have hS0 : 0 ≤ S := by positivity
  have hsS : ∀ k, ‖s k‖ ≤ S := fun k =>
    RN8.norm_le_of_coord (s k) (B * V) (by positivity) (fun i =>
      (hsv k i).trans (mul_le_mul_of_nonneg_left (hvb k i) hB.le))
  -- Hessian bound
  obtain ⟨δ, hδ, hδD⟩ := hL.exists_cthickening_subset_open hDo hLD
  have hK : IsCompact (Metric.cthickening δ L) := hL.cthickening
  have hHc : ContinuousOn (fun w => fderiv ℝ (gradient f) w) D := by
    have hc1 : ContDiffOn ℝ 1 (gradient f) D := fun y hy =>
      (RN8.grad_C1 f D hDo hf hy).contDiffWithinAt
    exact hc1.continuousOn_fderiv_of_isOpen hDo le_rfl
  obtain ⟨M0, hM0⟩ := hK.exists_bound_of_continuousOn (hHc.mono hδD)
  set M := |M0| with hMdef
  have hM : 0 ≤ M := abs_nonneg _
  have hMK : ∀ w ∈ Metric.cthickening δ L, ‖fderiv ℝ (gradient f) w‖ ≤ M :=
    fun w hw => (hM0 w hw).trans (le_abs_self _)
  set α0 := min ρ (min (1 / (B + 1)) (δ / (S + 1))) with hα0def
  have hα0 : 0 < α0 := lt_min hρ (lt_min (by positivity) (by positivity))
  have key : ∀ k, α k < α0 →
      (1 - σu) * (-inner ℝ (gradient f (x k)) (s k)) ≤ 2 * M * S ^ 2 * α k := by
    intro k hk
    have hαpos := (hstep k).2.1
    have hkρ : α k < ρ := lt_of_lt_of_le hk (min_le_left _ _)
    have hkB : α k < 1 / (B + 1) :=
      lt_of_lt_of_le hk ((min_le_right _ _).trans (min_le_left _ _))
    have hkS : α k < δ / (S + 1) :=
      lt_of_lt_of_le hk ((min_le_right _ _).trans (min_le_right _ _))
    have hαB : α k * B < 1 := by
      rw [lt_div_iff₀ (by linarith)] at hkB; nlinarith
    have hαS : α k * S ≤ δ := by
      rw [lt_div_iff₀ (by linarith)] at hkS; nlinarith
    have hz : x (k + 1) = reflect l u (x k + α k • s k) := by
      rw [(hstep k).2.2.2.2.2]; simp [reflPath]
    have hzi : ∀ i, x (k + 1) i = reflectCoord (l i) (u i) (x k i + α k * s k i) := by
      intro i; rw [hz]
      show reflectCoord (l i) (u i) ((x k + α k • s k) i) = _
      simp
    have hlin : inner ℝ (gradient f (x k)) (x (k + 1) - x k) ≤
        α k * inner ℝ (gradient f (x k)) (s k) := by
      rw [← inner_smul_right, RN8.inner_coord, RN8.inner_coord]
      refine Finset.sum_le_sum (fun i _ => ?_)
      have hc := RN8.coord_key (l i) (u i) (x k i) (s k i) (gradient f (x k) i) (α k) B
        (hint k i).1 (hint k i).2 hαpos.le hB.le hαB (hsv k i)
      simp only [PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul, hzi i]
      exact hc
    have hnorm : ‖x (k + 1) - x k‖ ≤ α k * ‖s k‖ := by
      rw [hz]
      refine (RN8.reflect_norm_le l u (x k) _ (hbox _ (hint k))).trans (le_of_eq ?_)
      rw [add_sub_cancel_left, norm_smul, Real.norm_of_nonneg hαpos.le]
    have hnormδ : ‖x (k + 1) - x k‖ ≤ δ :=
      hnorm.trans ((mul_le_mul_of_nonneg_left (hsS k) hαpos.le).trans hαS)
    have hballK : Metric.closedBall (x k) ‖x (k + 1) - x k‖ ⊆ Metric.cthickening δ L :=
      (Metric.closedBall_subset_closedBall hnormδ).trans
        (Metric.closedBall_subset_cthickening (hxL k) δ)
    have htay := RN8.taylor_up f D hDo hf (x k) (x (k + 1)) M hM (hballK.trans hδD)
      (fun w hw => hMK w (hballK hw))
    have hxK : x k ∈ Metric.cthickening δ L := Metric.self_subset_cthickening L (hxL k)
    have hhq : -(M * ‖s k‖ ^ 2) ≤ min (hq f (x k) (s k)) 0 := by
      refine le_min ?_ (by have := norm_nonneg (s k); nlinarith)
      have h1 := abs_real_inner_le_norm (fderiv ℝ (gradient f) (x k) (s k)) (s k)
      have h2 := (fderiv ℝ (gradient f) (x k)).le_opNorm (s k)
      have h3 := hMK _ hxK
      have h4 : ‖fderiv ℝ (gradient f) (x k) (s k)‖ * ‖s k‖ ≤ M * ‖s k‖ ^ 2 := by
        have := mul_le_mul_of_nonneg_right h2 (norm_nonneg (s k))
        have h5 := mul_le_mul_of_nonneg_right h3 (sq_nonneg ‖s k‖)
        nlinarith
      have := neg_abs_le (inner ℝ (fderiv ℝ (gradient f) (x k) (s k)) (s k))
      show -(M * ‖s k‖ ^ 2) ≤ inner ℝ (fderiv ℝ (gradient f) (x k) (s k)) (s k)
      linarith
    have h35 : cond35 f σu (x k) (s k) (α k) (x (k + 1)) := by
      rcases (hstep k).2.2.2.2.1 with h | h
      · exact h
      · exact absurd h (not_lt.mpr hkρ.le)
    unfold cond35 at h35
    have htay' : f (x (k + 1)) - f (x k) ≤
        α k * (-(-inner ℝ (gradient f (x k)) (s k))) + M * (α k * ‖s k‖) ^ 2 := by
      have hsq : ‖x (k + 1) - x k‖ ^ 2 ≤ (α k * ‖s k‖) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) hnorm 2
      have := mul_le_mul_of_nonneg_left hsq hM
      linarith
    refine RN8.arith_key (α k) (-inner ℝ (gradient f (x k)) (s k)) ‖s k‖ S M
      (min (hq f (x k) (s k)) 0) σu (f (x (k + 1))) (f (x k)) hαpos
      (neg_nonneg.mpr (hgs k)) (norm_nonneg _) (hsS k) hM (by linarith) hσu hhq ?_ htay'
    simpa using h35
  -- t_k -> 0
  set T : ℕ → ℝ := fun k => -inner ℝ (gradient f (x k)) (s k) with hTdef
  have hT0 : ∀ k, 0 ≤ T k := fun k => neg_nonneg.mpr (hgs k)
  have hσ1 : 0 < 1 - σu := by linarith
  have hT2 : ∀ k, T k ^ 2 ≤ 2 * M * S ^ 2 / (1 - σu) * P k + (P k / α0) ^ 2 := by
    intro k
    have hPk : P k = α k * T k := rfl
    have hC : 0 ≤ 2 * M * S ^ 2 / (1 - σu) := by positivity
    rcases lt_or_ge (α k) α0 with hk | hk
    · have h1 := key k hk
      have h2 : (1 - σu) * T k ^ 2 ≤ 2 * M * S ^ 2 * P k := by
        rw [hPk]
        have := mul_le_mul_of_nonneg_right h1 (hT0 k)
        show (1 - σu) * T k ^ 2 ≤ 2 * M * S ^ 2 * (α k * T k)
        nlinarith
      have h3 : T k ^ 2 ≤ 2 * M * S ^ 2 / (1 - σu) * P k := by
        rw [div_mul_eq_mul_div, le_div_iff₀ hσ1]; linarith
      have := sq_nonneg (P k / α0)
      linarith
    · have h1 : T k ≤ P k / α0 := by
        rw [le_div_iff₀ hα0, hPk]
        exact mul_le_mul_of_nonneg_left hk (hT0 k) |>.trans_eq (mul_comm _ _)
      have h2 : T k ^ 2 ≤ (P k / α0) ^ 2 := pow_le_pow_left₀ (hT0 k) h1 2
      have := mul_nonneg hC (hP0 k)
      linarith
  have hT2t : Tendsto (fun k => T k ^ 2) atTop (𝓝 0) := by
    refine squeeze_zero (fun k => sq_nonneg _) hT2 ?_
    have := (hPt.const_mul (2 * M * S ^ 2 / (1 - σu))).add ((hPt.div_const α0).pow 2)
    simpa using this
  have hTt : Tendsto T atTop (𝓝 0) := by
    have := (Real.continuous_sqrt.tendsto 0).comp hT2t
    rw [Real.sqrt_zero] at this
    refine this.congr (fun k => ?_)
    simp [Function.comp_def, Real.sqrt_sq (hT0 k)]
  have hsg : Tendsto (fun k => inner ℝ (s k) (gradient f (x k))) atTop (𝓝 0) := by
    have := hTt.neg
    simp only [neg_zero] at this
    refine this.congr (fun k => ?_)
    simp [hTdef, real_inner_comm]
  have hdG := hcons hsg
  -- D^2 g -> 0
  have hbd : ∀ k, ‖dSqG l u f (x k)‖ ≤ Real.sqrt V * ‖dG l u f (x k)‖ := by
    intro k
    rw [← Real.norm_of_nonneg (Real.sqrt_nonneg V), ← norm_smul]
    apply RN8.norm_le_norm_of_coord
    intro i
    rw [PiLp.smul_apply, smul_eq_mul]
    show |(|vVec l u f (x k) i| * gradient f (x k) i)| ≤
      |Real.sqrt V * (Real.sqrt |vVec l u f (x k) i| * gradient f (x k) i)|
    have hq0 := abs_nonneg (vVec l u f (x k) i)
    have hsq := Real.mul_self_sqrt hq0
    have hle : Real.sqrt |vVec l u f (x k) i| ≤ Real.sqrt V := Real.sqrt_le_sqrt (hvb k i)
    have hs0 := Real.sqrt_nonneg |vVec l u f (x k) i|
    rw [abs_mul, abs_mul, abs_mul, abs_abs, abs_of_nonneg (Real.sqrt_nonneg V),
      abs_of_nonneg hs0]
    have hg := abs_nonneg (gradient f (x k) i)
    nlinarith [mul_le_mul_of_nonneg_right hle (mul_nonneg hs0 hg)]
  refine squeeze_zero_norm hbd ?_
  have := (hdG.norm).const_mul (Real.sqrt V)
  simpa using this
