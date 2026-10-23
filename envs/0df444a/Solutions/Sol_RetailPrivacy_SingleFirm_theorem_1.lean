-- Prove2me | solution 1 for RetailPrivacy.SingleFirm.theorem_1
-- status  : ACCEPTED   (prove)
-- author  : @frknbls
-- created : 2026-10-22T16:58:54.91278+00:00
-- url     : https://prove2.me/submissions/1f0f4ad1-284b-489a-bd09-139ff16fe982

import Definitions.Def_RetailPrivacy_SingleFirm_Model

namespace RetailPrivacy.SingleFirm

open MeasureTheory

noncomputable section

def clamp01 (t : ℝ) : ℝ := max 0 (min 1 t)

lemma clamp01_nonneg (t : ℝ) : 0 ≤ clamp01 t := le_max_left _ _

lemma clamp01_of_nonpos {t : ℝ} (h : t ≤ 0) : clamp01 t = 0 := by
  unfold clamp01; rw [min_eq_right (by linarith)]; exact max_eq_left h

lemma clamp01_of_mem {t : ℝ} (h0 : 0 ≤ t) (h1 : t ≤ 1) : clamp01 t = t := by
  unfold clamp01; rw [min_eq_right h1]; exact max_eq_right h0

lemma clamp01_of_ge {t : ℝ} (h : 1 ≤ t) : clamp01 t = 1 := by
  unfold clamp01; rw [min_eq_left h]; norm_num

lemma vol_Icc_toReal (a b : ℝ) : (volume (Set.Icc a b)).toReal = max (b - a) 0 := by
  rw [Real.volume_Icc, ENNReal.toReal_ofReal']

lemma vol_le (t : ℝ) :
    (volume {θ : ℝ | θ ∈ Set.Icc 0 1 ∧ θ ≤ t}).toReal = clamp01 t := by
  have : {θ : ℝ | θ ∈ Set.Icc 0 1 ∧ θ ≤ t} = Set.Icc 0 (min 1 t) := by
    ext θ; simp only [Set.mem_setOf_eq, Set.mem_Icc, le_min_iff]; tauto
  rw [this, vol_Icc_toReal, sub_zero, max_comm]; rfl

lemma demand_true (v δ p r : ℝ) (hδ1 : δ < 1) :
    demand true v δ p r = clamp01 (max (v - p) ((v - p - r * δ) / (1 - δ))) := by
  unfold demand
  rw [← vol_le]
  congr 2
  ext θ
  simp only [Set.mem_setOf_eq, buyUtil, if_true, utilHide, utilDisclose, le_max_iff]
  have he : 0 < 1 - δ := by linarith
  rw [le_div_iff₀ he]
  constructor <;> rintro ⟨h1, h2⟩ <;> refine ⟨h1, ?_⟩ <;> rcases h2 with h2 | h2
  · left; linarith
  · right; linarith
  · left; linarith
  · right; linarith

lemma demand_false (v δ p r : ℝ) : demand false v δ p r = clamp01 (v - p) := by
  unfold demand
  rw [← vol_le]
  congr 2
  ext θ
  simp only [Set.mem_setOf_eq, buyUtil, Bool.false_eq_true, if_false, utilHide]
  constructor <;> rintro ⟨h1, h2⟩ <;> refine ⟨h1, ?_⟩ <;> linarith

lemma discloseQty_eq (v δ p r : ℝ) (hδ0 : 0 < δ) (hδ1 : δ < 1) :
    discloseQty v δ p r = max (min 1 ((v - p - r * δ) / (1 - δ)) - max 0 r) 0 := by
  unfold discloseQty
  have he : 0 < 1 - δ := by linarith
  have : {θ : ℝ | θ ∈ Set.Icc 0 1 ∧ utilHide v p θ ≤ utilDisclose v δ p r θ ∧
      0 ≤ utilDisclose v δ p r θ} = Set.Icc (max 0 r) (min 1 ((v - p - r * δ) / (1 - δ))) := by
    ext θ
    simp only [Set.mem_setOf_eq, Set.mem_Icc, utilHide, utilDisclose, max_le_iff, le_min_iff]
    rw [le_div_iff₀ he]
    constructor
    · rintro ⟨⟨h1, h2⟩, h3, h4⟩
      refine ⟨⟨h1, ?_⟩, h2, by linarith⟩
      by_contra hc; push_neg at hc
      have : δ * θ < δ * r := mul_lt_mul_of_pos_left hc hδ0
      linarith
    · rintro ⟨⟨h1, h2⟩, h3, h4⟩
      refine ⟨⟨h1, h3⟩, ?_, by linarith⟩
      nlinarith
  rw [this, vol_Icc_toReal]

lemma int_lin {f : ℝ → ℝ} {a b α β : ℝ} (hab : a ≤ b)
    (h : ∀ θ ∈ Set.Icc a b, f θ = α - β * θ) :
    ∫ θ in a..b, f θ = α * (b - a) - β * (b ^ 2 - a ^ 2) / 2 := by
  rw [intervalIntegral.integral_congr (g := fun θ => α - β * θ)]
  · rw [intervalIntegral.integral_sub intervalIntegrable_const
      ((by fun_prop : Continuous fun x : ℝ => β * x).intervalIntegrable _ _)]
    rw [intervalIntegral.integral_const_mul, integral_id, intervalIntegral.integral_const]
    simp; ring
  · intro θ hθ
    rw [Set.uIcc_of_le hab] at hθ
    exact h θ hθ

lemma cs_formula (v δ p r T : ℝ) (hδ0 : 0 < δ) (hδ1 : δ < 1) (h0r : 0 ≤ r) (hrT : r ≤ T)
    (hT1 : T ≤ 1) (hx : v - p = r * δ + (1 - δ) * T) :
    consumerSurplus true v δ p r = r * (v - p) - r ^ 2 / 2 + (1 - δ) * (T - r) ^ 2 / 2 := by
  unfold consumerSurplus
  have hcont : Continuous (fun θ => max 0 (buyUtil true v δ p r θ)) := by
    simp only [buyUtil, if_true, utilHide, utilDisclose]
    fun_prop
  have hi : ∀ a b : ℝ, IntervalIntegrable (fun θ => max 0 (buyUtil true v δ p r θ)) volume a b :=
    fun a b => hcont.intervalIntegrable a b
  rw [← intervalIntegral.integral_add_adjacent_intervals (hi 0 r) (hi r 1),
    ← intervalIntegral.integral_add_adjacent_intervals (hi r T) (hi T 1)]
  rw [int_lin (α := v - p) (β := 1) h0r, int_lin (α := v - p - r * δ) (β := 1 - δ) hrT,
    int_lin (α := 0) (β := 0) hT1]
  · have : v - p - r * δ = (1 - δ) * T := by linarith
    linear_combination (T - r) * this
  · intro θ hθ
    simp only [buyUtil, if_true, utilHide, utilDisclose]
    have h1 : v - p - (1 - δ) * θ - r * δ ≤ 0 := by nlinarith [hθ.1]
    have h2 : v - p - θ ≤ v - p - (1 - δ) * θ - r * δ := by nlinarith [hθ.1]
    simp; constructor <;> linarith
  · intro θ hθ
    simp only [buyUtil, if_true, utilHide, utilDisclose]
    have h1 : 0 ≤ v - p - (1 - δ) * θ - r * δ := by nlinarith [hθ.2]
    have h2 : v - p - θ ≤ v - p - (1 - δ) * θ - r * δ := by nlinarith [hθ.1]
    rw [max_eq_right h2, max_eq_right h1]; ring
  · intro θ hθ
    simp only [buyUtil, if_true, utilHide, utilDisclose]
    have h2 : v - p - (1 - δ) * θ - r * δ ≤ v - p - θ := by nlinarith [hθ.2]
    have h1 : 0 ≤ v - p - θ := by nlinarith [hθ.2]
    rw [max_eq_left h2, max_eq_right h1]; ring

/-! ### A generic one-dimensional profit shape -/

def G (v m k q y : ℝ) : ℝ := if y ≤ 0 then 0 else if y ≤ 1 then v * y - m * y ^ 2 else v - k * y + q

def ystar (v m : ℝ) : ℝ := if v ≤ 2 * m then v / (2 * m) else 1

def Gstar (v m : ℝ) : ℝ := if v ≤ 2 * m then v ^ 2 / (4 * m) else v - m

lemma ystar_pos {v m : ℝ} (hv : 0 < v) (hm : 0 < m) : 0 < ystar v m := by
  unfold ystar; split_ifs <;> positivity

lemma ystar_le_one {v m : ℝ} (hm : 0 < m) : ystar v m ≤ 1 := by
  unfold ystar; split_ifs with h
  · rw [div_le_one (by positivity)]; exact h
  · exact le_rfl

lemma Gstar_eq {v m : ℝ} (hm : 0 < m) : Gstar v m = v * ystar v m - m * ystar v m ^ 2 := by
  unfold Gstar ystar; split_ifs
  · field_simp; ring
  · ring

lemma Gstar_pos {v m : ℝ} (hv : 0 < v) (hm : 0 < m) : 0 < Gstar v m := by
  unfold Gstar; split_ifs with h
  · positivity
  · push_neg at h; linarith

lemma G_opt {v m k q : ℝ} (hv : 0 < v) (hm : 0 < m) (hq : 0 ≤ q) (hk : k = m + q) :
    (∀ y, G v m k q y ≤ Gstar v m) ∧ G v m k q (ystar v m) = Gstar v m ∧
    (∀ y, Gstar v m ≤ G v m k q y → y = ystar v m) := by
  have hsq : ∀ y, v ^ 2 / (4 * m) - (v * y - m * y ^ 2) = m * (y - v / (2 * m)) ^ 2 := by
    intro y; field_simp; ring
  have hsq2 : v ^ 2 / (4 * m) - (v - m) = (v - 2 * m) ^ 2 / (4 * m) := by
    field_simp; ring
  have hsq2' : 0 ≤ (v - 2 * m) ^ 2 / (4 * m) := by positivity
  have hpos := ystar_pos hv hm
  have hle := ystar_le_one (v := v) hm
  have G1 : ∀ y, y ≤ 0 → G v m k q y = 0 := fun y h => by simp [G, h]
  have G2 : ∀ y, 0 < y → y ≤ 1 → G v m k q y = v * y - m * y ^ 2 := fun y h h' => by
    simp [G, not_le.mpr h, h']
  have G3 : ∀ y, 1 < y → G v m k q y = v - k * y + q := fun y h => by
    simp [G, not_le.mpr h, not_le.mpr (show (0:ℝ) < y by linarith)]
  have hG4 : 0 < v ^ 2 / (4 * m) := by positivity
  refine ⟨?_, ?_, ?_⟩
  · intro y
    rcases le_or_gt v (2 * m) with hv2 | hv2
    · have hS : Gstar v m = v ^ 2 / (4 * m) := by simp [Gstar, hv2]
      rw [hS]
      rcases le_or_gt y 0 with hy | hy
      · rw [G1 y hy]; exact hG4.le
      rcases le_or_gt y 1 with hy1 | hy1
      · rw [G2 y hy hy1]; nlinarith [hsq y, sq_nonneg (y - v / (2 * m))]
      · rw [G3 y hy1]; nlinarith
    · have hS : Gstar v m = v - m := by simp [Gstar, not_le.mpr hv2]
      rw [hS]
      rcases le_or_gt y 0 with hy | hy
      · rw [G1 y hy]; linarith
      rcases le_or_gt y 1 with hy1 | hy1
      · rw [G2 y hy hy1]; nlinarith [mul_nonneg (sub_nonneg.mpr hy1) (show 0 ≤ v - m * (1 + y) by nlinarith)]
      · rw [G3 y hy1]; nlinarith
  · rw [G2 _ hpos hle, Gstar_eq hm]
  · intro y hy
    rcases le_or_gt v (2 * m) with hv2 | hv2
    · have hS : Gstar v m = v ^ 2 / (4 * m) := by simp [Gstar, hv2]
      have hY : ystar v m = v / (2 * m) := by simp [ystar, hv2]
      rw [hS] at hy; rw [hY]
      rcases le_or_gt y 0 with hy0 | hy0
      · rw [G1 y hy0] at hy; linarith
      rcases le_or_gt y 1 with hy1 | hy1
      · rw [G2 y hy0 hy1] at hy
        have h := hsq y
        have : m * (y - v / (2 * m)) ^ 2 ≤ 0 := by linarith
        have : (y - v / (2 * m)) ^ 2 = 0 := by
          apply le_antisymm _ (sq_nonneg _)
          by_contra hc; push_neg at hc
          have := mul_pos hm hc; linarith
        have := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp this
        linarith
      · rw [G3 y hy1] at hy; nlinarith
    · have hS : Gstar v m = v - m := by simp [Gstar, not_le.mpr hv2]
      have hY : ystar v m = 1 := by simp [ystar, not_le.mpr hv2]
      rw [hS] at hy; rw [hY]
      rcases le_or_gt y 0 with hy0 | hy0
      · rw [G1 y hy0] at hy; linarith
      rcases le_or_gt y 1 with hy1 | hy1
      · rw [G2 y hy0 hy1] at hy
        by_contra hne
        have hy1' : y < 1 := lt_of_le_of_ne hy1 hne
        nlinarith [mul_pos (sub_pos.mpr hy1') (show 0 < v - m * (1 + y) by nlinarith)]
      · rw [G3 y hy1] at hy; nlinarith

lemma Gstar_anti {v m₁ m₂ : ℝ} (hv : 0 < v) (h1 : 0 < m₁) (h12 : m₁ < m₂) :
    Gstar v m₂ < Gstar v m₁ := by
  unfold Gstar
  have h2 : 0 < m₂ := by linarith
  split_ifs with ha hb hb
  · rw [div_lt_div_iff₀ (by positivity) (by positivity)]
    have : 0 < v ^ 2 := by positivity
    nlinarith
  · push_neg at hb
    rw [div_lt_iff₀ (by positivity)]
    nlinarith [mul_nonneg (sub_nonneg.mpr hb.le) (sub_nonneg.mpr ha)]
  · exfalso; push_neg at ha; linarith
  · linarith

/-! ### Model constants -/

def Kc (c δ : ℝ) : ℝ := 2 * c * (1 - δ) + δ

lemma KZ_id (c δ : ℝ) : Kc c δ - δ ^ 2 = Zc c δ * (1 - δ) := by unfold Kc Zc; ring

lemma MZK_id (c δ : ℝ) : Mc c δ = Zc c δ * Kc c δ - c * δ ^ 2 := by unfold Mc Kc Zc; ring

lemma K_le_Z (c δ : ℝ) (hc : 0 < c) (hδ0 : 0 < δ) : Kc c δ ≤ Zc c δ := by
  unfold Kc Zc; nlinarith

/-! ### Policy C and no-collection profits -/

lemma profit_C_true {v c δ p s r : ℝ} (hδ0 : 0 < δ) (hδ1 : δ < 1)
    (h : IsREE .C true v c δ p s r) :
    firmProfit true v c δ p (s, r) = G v (1 - δ) (1 - δ) 0 ((v - p) / (1 - δ)) := by
  simp only [IsREE, if_true] at h
  obtain ⟨rfl, -⟩ := h
  have he : 0 < 1 - δ := by linarith
  unfold firmProfit dataProfit
  simp only
  rw [demand_true _ _ _ _ hδ1]
  set y := (v - p) / (1 - δ) with hy
  have hx : v - p = (1 - δ) * y := by rw [hy]; field_simp
  rw [hx, show (1 - δ) * y - 0 * δ = (1 - δ) * y by ring, mul_div_cancel_left₀ _ he.ne']
  have hp : p = v - (1 - δ) * y := by linarith
  rcases le_or_gt y 0 with hy0 | hy0
  · rw [clamp01_of_nonpos (max_le (by nlinarith) hy0)]
    simp [G, hy0]
  rcases le_or_gt y 1 with hy1 | hy1
  · rw [max_eq_right (by nlinarith), clamp01_of_mem hy0.le hy1]
    simp [G, not_le.mpr hy0, hy1]; rw [hp]; ring
  · rw [max_eq_right (by nlinarith), clamp01_of_ge hy1.le]
    simp [G, not_le.mpr hy0, not_le.mpr hy1]; rw [hp]

lemma profit_false {pol : Policy} {v c δ p s r : ℝ}
    (h : IsREE pol false v c δ p s r) :
    firmProfit false v c δ p (s, r) = G v 1 1 0 (v - p) := by
  simp only [IsREE, Bool.false_eq_true, if_false] at h
  obtain ⟨rfl, rfl⟩ := h
  unfold firmProfit dataProfit
  simp only
  rw [demand_false]
  set y := v - p with hy
  have hp : p = v - y := by linarith
  rcases le_or_gt y 0 with hy0 | hy0
  · rw [clamp01_of_nonpos hy0]; simp [G, hy0]
  rcases le_or_gt y 1 with hy1 | hy1
  · rw [clamp01_of_mem hy0.le hy1]; simp [G, not_le.mpr hy0, hy1]; rw [hp]; ring
  · rw [clamp01_of_ge hy1.le]; simp [G, not_le.mpr hy0, not_le.mpr hy1]; rw [hp]

/-! ### Policy R -/

def yR (v c δ p : ℝ) : ℝ := Zc c δ * (v - p) / Kc c δ

def sR (v c δ p : ℝ) : ℝ := 2 * c / Zc c δ * clamp01 (yR v c δ p)

def rR (v c δ p : ℝ) : ℝ := δ / Zc c δ * clamp01 (yR v c δ p)

lemma Z_pos {c δ : ℝ} (hc : 0 < c) (hδ0 : 0 < δ) : 0 < Zc c δ := by unfold Zc; linarith

lemma K_pos {c δ : ℝ} (hc : 0 < c) (hδ0 : 0 < δ) (hδ1 : δ < 1) : 0 < Kc c δ := by
  unfold Kc; nlinarith

lemma rR_eq {v c δ p : ℝ} (hc : 0 < c) (hδ0 : 0 < δ) :
    rR v c δ p = δ * sR v c δ p / (2 * c) := by
  unfold rR sR; field_simp


lemma num_id {c δ : ℝ} (hc : 0 < c) (hδ0 : 0 < δ) (y : ℝ) :
    Kc c δ * y / Zc c δ - δ / Zc c δ * y * δ = (1 - δ) * y := by
  have hZ := Z_pos hc hδ0
  have : Kc c δ * y / Zc c δ - δ / Zc c δ * y * δ = (Kc c δ - δ ^ 2) * y / Zc c δ := by ring
  rw [this, KZ_id]; field_simp

lemma one_sub_id {c δ : ℝ} (hc : 0 < c) (hδ0 : 0 < δ) (y : ℝ) :
    y - δ / Zc c δ * y = 2 * c / Zc c δ * y := by
  have hZ := Z_pos hc hδ0
  rw [show y - δ / Zc c δ * y = (Zc c δ - δ) / Zc c δ * y by rw [sub_div, div_self hZ.ne']; ring,
    show Zc c δ - δ = 2 * c by unfold Zc; ring]

lemma disclose_R_fix {v c δ p : ℝ} (hc : 0 < c) (hδ0 : 0 < δ) (hδ1 : δ < 1) :
    discloseQty v δ p (rR v c δ p) = sR v c δ p := by
  have he : 0 < 1 - δ := by linarith
  have hZ := Z_pos hc hδ0
  have hK := K_pos hc hδ0 hδ1
  have hKZ := KZ_id c δ
  have hKleZ := K_le_Z c δ hc hδ0
  rw [discloseQty_eq _ _ _ _ hδ0 hδ1]
  unfold rR sR
  set y := yR v c δ p with hy
  have hx : v - p = Kc c δ * y / Zc c δ := by rw [hy, yR]; field_simp
  rw [hx]
  rcases le_or_gt y 0 with hy0 | hy0
  · rw [clamp01_of_nonpos hy0]
    simp only [mul_zero, zero_mul, sub_zero, max_self]
    have : Kc c δ * y / Zc c δ / (1 - δ) ≤ 0 :=
      div_nonpos_of_nonpos_of_nonneg (div_nonpos_of_nonpos_of_nonneg
        (mul_nonpos_of_nonneg_of_nonpos hK.le hy0) hZ.le) he.le
    rw [min_eq_right (by linarith), max_eq_right this]
  rcases le_or_gt y 1 with hy1 | hy1
  · rw [clamp01_of_mem hy0.le hy1]
    have hT : (Kc c δ * y / Zc c δ - δ / Zc c δ * y * δ) / (1 - δ) = y := by
      rw [num_id hc hδ0, mul_div_cancel_left₀ _ he.ne']
    rw [hT, min_eq_right hy1, max_eq_right (mul_nonneg (div_nonneg hδ0.le hZ.le) hy0.le),
      one_sub_id hc hδ0, max_eq_left (mul_nonneg (div_nonneg (by linarith) hZ.le) hy0.le)]
  · rw [clamp01_of_ge hy1.le]
    have hT : 1 ≤ (Kc c δ * y / Zc c δ - δ / Zc c δ * 1 * δ) / (1 - δ) := by
      rw [le_div_iff₀ he]
      have : Kc c δ * y / Zc c δ - δ / Zc c δ * 1 * δ = (Kc c δ * y - δ ^ 2) / Zc c δ := by ring
      rw [this, le_div_iff₀ hZ]
      nlinarith
    rw [min_eq_left hT, max_eq_right (mul_nonneg (div_nonneg hδ0.le hZ.le) zero_le_one),
      one_sub_id hc hδ0, max_eq_left (mul_nonneg (div_nonneg (by linarith) hZ.le) zero_le_one)]

lemma disclose_anti {v c δ p s s' : ℝ} (hc : 0 < c) (hδ0 : 0 < δ) (hδ1 : δ < 1)
    (hss : s ≤ s') :
    discloseQty v δ p (δ * s' / (2 * c)) ≤ discloseQty v δ p (δ * s / (2 * c)) := by
  have he : 0 < 1 - δ := by linarith
  rw [discloseQty_eq _ _ _ _ hδ0 hδ1, discloseQty_eq _ _ _ _ hδ0 hδ1]
  have h1 : δ * s / (2 * c) ≤ δ * s' / (2 * c) := by gcongr
  have h2 : (v - p - δ * s' / (2 * c) * δ) / (1 - δ) ≤ (v - p - δ * s / (2 * c) * δ) / (1 - δ) := by
    gcongr
  gcongr

lemma REE_R_iff {v c δ p s r : ℝ} (hc : 0 < c) (hδ0 : 0 < δ) (hδ1 : δ < 1) :
    IsREE .R true v c δ p s r ↔ s = sR v c δ p ∧ r = rR v c δ p := by
  simp only [IsREE, if_true]
  have hfix := disclose_R_fix (v := v) (p := p) hc hδ0 hδ1
  have hrr := rR_eq (v := v) (p := p) hc hδ0
  constructor
  · rintro ⟨hmax, hs⟩
    have hs0 : 0 ≤ s := by rw [hs, discloseQty_eq _ _ _ _ hδ0 hδ1]; exact le_max_right _ _
    have hr : r = δ * s / (2 * c) := by
      have h := hmax (show δ * s / (2 * c) ∈ Set.Ici 0 by simp; positivity)
      simp only [dataProfit] at h
      have : c * (r - δ * s / (2 * c)) ^ 2 ≤ 0 := by
        have e1 : c * (r - δ * s / (2 * c)) ^ 2 =
            δ * s / (2 * c) * δ * s - c * (δ * s / (2 * c)) ^ 2 - (r * δ * s - c * r ^ 2) := by
          field_simp; ring
        rw [e1]; exact sub_nonpos.mpr h
      have h2 : (r - δ * s / (2 * c)) ^ 2 = 0 := by
        apply le_antisymm _ (sq_nonneg _)
        by_contra hcon; push_neg at hcon
        have := mul_pos hc hcon; linarith
      have := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp h2
      linarith
    rw [hr] at hs
    have hsR : s = sR v c δ p := by
      rw [hrr] at hfix
      rcases lt_trichotomy s (sR v c δ p) with hlt | heq | hgt
      · have := disclose_anti (v := v) (p := p) hc hδ0 hδ1 hlt.le
        rw [hfix, ← hs] at this; linarith
      · exact heq
      · have := disclose_anti (v := v) (p := p) hc hδ0 hδ1 hgt.le
        rw [hfix, ← hs] at this; linarith
    refine ⟨hsR, ?_⟩
    rw [hr, hrr, hsR]
  · rintro ⟨rfl, rfl⟩
    refine ⟨?_, hfix.symm⟩
    intro r' _
    show r' * δ * sR v c δ p - c * r' ^ 2 ≤ rR v c δ p * δ * sR v c δ p - c * rR v c δ p ^ 2
    rw [hrr]
    have : δ * sR v c δ p / (2 * c) * δ * sR v c δ p - c * (δ * sR v c δ p / (2 * c)) ^ 2 -
        (r' * δ * sR v c δ p - c * r' ^ 2) = c * (r' - δ * sR v c δ p / (2 * c)) ^ 2 := by
      field_simp; ring
    nlinarith [mul_nonneg hc.le (sq_nonneg (r' - δ * sR v c δ p / (2 * c)))]


lemma Mc_pos {c δ : ℝ} (hc : 0 < c) (hδ0 : 0 < δ) (hδ1 : δ < 1) : 0 < Mc c δ := by
  unfold Mc; nlinarith [mul_pos hc hδ0, mul_pos (mul_pos hc hc) (sub_pos.mpr hδ1), sq_nonneg δ]

lemma profit_R_true {v c δ p s r : ℝ} (hc : 0 < c) (hδ0 : 0 < δ) (hδ1 : δ < 1)
    (h : IsREE .R true v c δ p s r) :
    firmProfit true v c δ p (s, r) =
      G v (Mc c δ / Zc c δ ^ 2) (Kc c δ / Zc c δ) (c * δ ^ 2 / Zc c δ ^ 2) (yR v c δ p) := by
  rw [REE_R_iff hc hδ0 hδ1] at h
  obtain ⟨rfl, rfl⟩ := h
  have he : 0 < 1 - δ := by linarith
  have hZ := Z_pos hc hδ0
  have hK := K_pos hc hδ0 hδ1
  have hKZ := KZ_id c δ
  have hMZK := MZK_id c δ
  have hKleZ := K_le_Z c δ hc hδ0
  unfold firmProfit dataProfit sR rR
  simp only
  rw [demand_true _ _ _ _ hδ1]
  set y := yR v c δ p with hy
  have hx : v - p = Kc c δ * y / Zc c δ := by rw [hy, yR]; field_simp
  have hp : p = v - Kc c δ * y / Zc c δ := by linarith
  rw [hx]
  have hZne : Zc c δ ≠ 0 := hZ.ne'
  rcases le_or_gt y 0 with hy0 | hy0
  · rw [clamp01_of_nonpos hy0]
    have h1 : Kc c δ * y / Zc c δ ≤ 0 :=
      div_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonneg_of_nonpos hK.le hy0) hZ.le
    have h2 : (Kc c δ * y / Zc c δ - δ / Zc c δ * 0 * δ) / (1 - δ) ≤ 0 := by
      rw [mul_zero, zero_mul, sub_zero]
      exact div_nonpos_of_nonpos_of_nonneg h1 he.le
    rw [clamp01_of_nonpos (max_le h1 h2)]
    simp [G, hy0]
  rcases le_or_gt y 1 with hy1 | hy1
  · rw [clamp01_of_mem hy0.le hy1]
    have hT : (Kc c δ * y / Zc c δ - δ / Zc c δ * y * δ) / (1 - δ) = y := by
      rw [num_id hc hδ0, mul_div_cancel_left₀ _ he.ne']
    have hle : Kc c δ * y / Zc c δ ≤ y := by
      rw [div_le_iff₀ hZ]; nlinarith
    have G2 : G v (Mc c δ / Zc c δ ^ 2) (Kc c δ / Zc c δ) (c * δ ^ 2 / Zc c δ ^ 2) y =
        v * y - Mc c δ / Zc c δ ^ 2 * y ^ 2 := by simp [G, not_le.mpr hy0, hy1]
    rw [hT, max_eq_right hle, clamp01_of_mem hy0.le hy1, G2, hp, hMZK]
    field_simp
    ring
  · rw [clamp01_of_ge hy1.le]
    have hT : 1 ≤ (Kc c δ * y / Zc c δ - δ / Zc c δ * 1 * δ) / (1 - δ) := by
      rw [le_div_iff₀ he]
      have : Kc c δ * y / Zc c δ - δ / Zc c δ * 1 * δ = (Kc c δ * y - δ ^ 2) / Zc c δ := by ring
      rw [this, le_div_iff₀ hZ]
      nlinarith
    have G3 : G v (Mc c δ / Zc c δ ^ 2) (Kc c δ / Zc c δ) (c * δ ^ 2 / Zc c δ ^ 2) y =
        v - Kc c δ / Zc c δ * y + c * δ ^ 2 / Zc c δ ^ 2 := by
      simp [G, not_le.mpr hy0, not_le.mpr hy1]
    rw [clamp01_of_ge (le_max_of_le_right hT), G3, hp]
    field_simp
    ring

/-! ### Generic SPE characterization -/

lemma spe_unique {pol : Policy} {v c δ m k q pstar : ℝ} {yf : ℝ → ℝ}
    (hv : 0 < v) (hm : 0 < m) (hm1 : m < 1) (hq : 0 ≤ q) (hk : k = m + q)
    (hT : ∀ p (sr : ℝ × ℝ), IsREE pol true v c δ p sr.1 sr.2 →
      firmProfit true v c δ p sr = G v m k q (yf p))
    (hF : ∀ p (sr : ℝ × ℝ), IsREE pol false v c δ p sr.1 sr.2 →
      firmProfit false v c δ p sr = G v 1 1 0 (v - p))
    (hps : yf pstar = ystar v m)
    (P : Profile) (h : IsSPE pol v c δ P) :
    P.collect = true ∧ yf (P.price true) = ystar v m ∧ eqProfit v c δ P = Gstar v m := by
  obtain ⟨h1, h2, h3⟩ := h
  obtain ⟨Tle, Teq, Tuniq⟩ := G_opt (k := k) hv hm hq hk
  obtain ⟨Fle, Feq, -⟩ := G_opt (k := 1) (q := 0) hv one_pos le_rfl (by ring)
  have eT : firmProfit true v c δ (P.price true) (P.resp true (P.price true)) = Gstar v m := by
    rw [hT _ _ (h1 true _)]
    apply le_antisymm (Tle _)
    have := h2 true pstar
    rw [hT _ _ (h1 true _), hT _ _ (h1 true _), hps, Teq] at this
    exact this
  have hy : yf (P.price true) = ystar v m := by
    apply Tuniq
    rw [← hT _ _ (h1 true _), eT]
  have eF : firmProfit false v c δ (P.price false) (P.resp false (P.price false)) = Gstar v 1 := by
    rw [hF _ _ (h1 false _)]
    apply le_antisymm (Fle _)
    have := h2 false (v - ystar v 1)
    rw [hF _ _ (h1 false _), hF _ _ (h1 false _), sub_sub_cancel, Feq] at this
    exact this
  have hcol : P.collect = true := by
    by_contra hne
    have hf : P.collect = false := by simpa using hne
    have := h3 true
    rw [hf, eT, eF] at this
    have := Gstar_anti hv hm hm1
    linarith
  refine ⟨hcol, hy, ?_⟩
  unfold eqProfit eqResp eqPrice
  rw [hcol, eT]

lemma spe_exists {pol : Policy} {v c δ m k q pstar : ℝ} {yf : ℝ → ℝ}
    (hv : 0 < v) (hm : 0 < m) (hm1 : m < 1) (hq : 0 ≤ q) (hk : k = m + q)
    (hT : ∀ p (sr : ℝ × ℝ), IsREE pol true v c δ p sr.1 sr.2 →
      firmProfit true v c δ p sr = G v m k q (yf p))
    (hF : ∀ p (sr : ℝ × ℝ), IsREE pol false v c δ p sr.1 sr.2 →
      firmProfit false v c δ p sr = G v 1 1 0 (v - p))
    (hps : yf pstar = ystar v m)
    (resp : Bool → ℝ → ℝ × ℝ) (hresp : ∀ ℓ p, IsREE pol ℓ v c δ p (resp ℓ p).1 (resp ℓ p).2) :
    IsSPE pol v c δ ⟨true, fun ℓ => if ℓ then pstar else v - ystar v 1, resp⟩ := by
  obtain ⟨Tle, Teq, -⟩ := G_opt (k := k) hv hm hq hk
  obtain ⟨Fle, Feq, -⟩ := G_opt (k := 1) (q := 0) hv one_pos le_rfl (by ring)
  unfold IsSPE
  refine ⟨hresp, ?_, ?_⟩
  · intro ℓ p'
    cases ℓ
    · simp only [Bool.false_eq_true, ↓reduceIte]
      rw [hF _ _ (hresp false _), hF _ _ (hresp false _), sub_sub_cancel, Feq]
      exact Fle _
    · simp only [↓reduceIte]
      rw [hT _ _ (hresp true _), hT _ _ (hresp true _), hps, Teq]
      exact Tle _
  · intro ℓ'
    cases ℓ'
    · simp only [Bool.false_eq_true, ↓reduceIte]
      rw [hF _ _ (hresp false _), hT _ _ (hresp true _), sub_sub_cancel, Feq, hps, Teq]
      exact (Gstar_anti hv hm hm1).le
    · exact le_rfl

/-! ### Final inequalities -/

lemma final_ineq {v a b f : ℝ} (hv : 0 < v) (ha : 0 < a) (hab : a < b) (haf : a < f)
    (hfb : f < b) :
    (v ^ 2 * f < 4 * b ^ 2 * a → f * ystar v b ^ 2 / 2 < a * ystar v a ^ 2 / 2) ∧
    (4 * b ^ 2 * a < v ^ 2 * f → a * ystar v a ^ 2 / 2 < f * ystar v b ^ 2 / 2) ∧
    Gstar v b < Gstar v a ∧
    Gstar v b + f * ystar v b ^ 2 / 2 < Gstar v a + a * ystar v a ^ 2 / 2 := by
  have hb : 0 < b := by linarith
  have hf : 0 < f := by linarith
  have hfa : f * a < b ^ 2 := by nlinarith
  refine ⟨?_, ?_, Gstar_anti hv ha hab, ?_⟩
  · intro hlt
    rcases le_or_gt v (2 * a) with h1 | h1
    · have hya : ystar v a = v / (2 * a) := by simp [ystar, h1]
      have hyb : ystar v b = v / (2 * b) := by simp [ystar, show v ≤ 2 * b by linarith]
      rw [hya, hyb, div_pow, div_pow, ← sub_pos]
      have : a * (v ^ 2 / (2 * a) ^ 2) / 2 - f * (v ^ 2 / (2 * b) ^ 2) / 2
          = v ^ 2 * (b ^ 2 - f * a) / (8 * a * b ^ 2) := by field_simp; ring
      rw [this]; apply div_pos <;> nlinarith [sq_pos_of_pos hv]
    rcases le_or_gt v (2 * b) with h2 | h2
    · have hya : ystar v a = 1 := by simp [ystar, not_le.mpr h1]
      have hyb : ystar v b = v / (2 * b) := by simp [ystar, h2]
      rw [hya, hyb, div_pow, ← sub_pos]
      have : a * 1 ^ 2 / 2 - f * (v ^ 2 / (2 * b) ^ 2) / 2
          = (4 * b ^ 2 * a - v ^ 2 * f) / (8 * b ^ 2) := by field_simp; ring
      rw [this]; apply div_pos <;> nlinarith
    · exfalso
      have : (2 * b) ^ 2 < v ^ 2 := by
        exact pow_lt_pow_left₀ h2 (by linarith) (by norm_num)
      nlinarith
  · intro hlt
    rcases le_or_gt v (2 * a) with h1 | h1
    · exfalso
      have : v ^ 2 ≤ (2 * a) ^ 2 := pow_le_pow_left₀ hv.le h1 2
      nlinarith
    rcases le_or_gt v (2 * b) with h2 | h2
    · have hya : ystar v a = 1 := by simp [ystar, not_le.mpr h1]
      have hyb : ystar v b = v / (2 * b) := by simp [ystar, h2]
      rw [hya, hyb, div_pow, ← sub_pos]
      have : f * (v ^ 2 / (2 * b) ^ 2) / 2 - a * 1 ^ 2 / 2
          = (v ^ 2 * f - 4 * b ^ 2 * a) / (8 * b ^ 2) := by field_simp; ring
      rw [this]; apply div_pos <;> nlinarith
    · have hya : ystar v a = 1 := by simp [ystar, not_le.mpr h1]
      have hyb : ystar v b = 1 := by simp [ystar, not_le.mpr h2]
      rw [hya, hyb]; linarith
  · rcases le_or_gt v (2 * a) with h1 | h1
    · have hya : ystar v a = v / (2 * a) := by simp [ystar, h1]
      have hyb : ystar v b = v / (2 * b) := by simp [ystar, show v ≤ 2 * b by linarith]
      have hGa : Gstar v a = v ^ 2 / (4 * a) := by simp [Gstar, h1]
      have hGb : Gstar v b = v ^ 2 / (4 * b) := by simp [Gstar, show v ≤ 2 * b by linarith]
      rw [hya, hyb, hGa, hGb, div_pow, div_pow, ← sub_pos]
      have : v ^ 2 / (4 * a) + a * (v ^ 2 / (2 * a) ^ 2) / 2 -
          (v ^ 2 / (4 * b) + f * (v ^ 2 / (2 * b) ^ 2) / 2)
          = v ^ 2 * (3 * b ^ 2 - 2 * a * b - f * a) / (8 * a * b ^ 2) := by field_simp; ring
      have h3 : 0 < 3 * b ^ 2 - 2 * a * b - f * a := by nlinarith
      rw [this]; apply div_pos (mul_pos (pow_pos hv 2) h3); positivity
    rcases le_or_gt v (2 * b) with h2 | h2
    · have hya : ystar v a = 1 := by simp [ystar, not_le.mpr h1]
      have hyb : ystar v b = v / (2 * b) := by simp [ystar, h2]
      have hGa : Gstar v a = v - a := by simp [Gstar, not_le.mpr h1]
      have hGb : Gstar v b = v ^ 2 / (4 * b) := by simp [Gstar, h2]
      rw [hya, hyb, hGa, hGb, div_pow, ← sub_pos]
      have : v - a + a * 1 ^ 2 / 2 - (v ^ 2 / (4 * b) + f * (v ^ 2 / (2 * b) ^ 2) / 2)
          = (8 * b ^ 2 * v - 4 * a * b ^ 2 - 2 * b * v ^ 2 - f * v ^ 2) / (8 * b ^ 2) := by
        field_simp; ring
      rw [this]; apply div_pos _ (by positivity)
      nlinarith [mul_nonneg (mul_nonneg hb.le (sub_nonneg.mpr h1.le)) (sub_nonneg.mpr h2),
        mul_pos (mul_pos hb hb) (sub_pos.mpr h1),
        mul_nonneg (mul_nonneg hb.le ha.le) (sub_nonneg.mpr h2),
        mul_pos (sub_pos.mpr hfb) (pow_pos hv 2)]
    · have hya : ystar v a = 1 := by simp [ystar, not_le.mpr h1]
      have hyb : ystar v b = 1 := by simp [ystar, not_le.mpr h2]
      have hGa : Gstar v a = v - a := by simp [Gstar, not_le.mpr h1]
      have hGb : Gstar v b = v - b := by simp [Gstar, not_le.mpr h2]
      rw [hya, hyb, hGa, hGb]; linarith

/-! ### Consumer surplus on path -/

lemma cs_C {v δ p y : ℝ} (hδ0 : 0 < δ) (hδ1 : δ < 1) (hy0 : 0 ≤ y) (hy1 : y ≤ 1)
    (hx : v - p = (1 - δ) * y) :
    consumerSurplus true v δ p 0 = (1 - δ) * y ^ 2 / 2 := by
  rw [cs_formula v δ p 0 y hδ0 hδ1 le_rfl hy0 hy1 (by linarith)]
  ring

lemma cs_R {v c δ p : ℝ} (hc : 0 < c) (hδ0 : 0 < δ) (hδ1 : δ < 1)
    (hy0 : 0 ≤ yR v c δ p) (hy1 : yR v c δ p ≤ 1) :
    consumerSurplus true v δ p (rR v c δ p) = Fc c δ / Zc c δ ^ 2 * yR v c δ p ^ 2 / 2 := by
  have hZ := Z_pos hc hδ0
  have hK := K_pos hc hδ0 hδ1
  have hKZ := KZ_id c δ
  set y := yR v c δ p with hy
  have hx : v - p = Kc c δ * y / Zc c δ := by rw [hy, yR]; field_simp
  have hr : rR v c δ p = δ / Zc c δ * y := by rw [rR, clamp01_of_mem hy0 hy1]
  rw [hr]
  have hrT : δ / Zc c δ * y ≤ y := by
    rw [div_mul_eq_mul_div, div_le_iff₀ hZ]
    have : δ ≤ Zc c δ := by unfold Zc; linarith
    nlinarith
  have hx' : v - p = δ / Zc c δ * y * δ + (1 - δ) * y := by
    rw [hx, ← num_id hc hδ0 y]; ring
  rw [cs_formula v δ p _ y hδ0 hδ1 (mul_nonneg (div_nonneg hδ0.le hZ.le) hy0) hrT hy1 hx']
  rw [hx]
  have hZne : Zc c δ ≠ 0 := hZ.ne'
  have hZc : Zc c δ = 2 * c + δ := rfl
  field_simp
  rw [hZc]; unfold Fc Kc
  ring

/-! ### Main theorem -/

theorem theorem_1 (c δ v : ℝ) (hc : 0 < c) (hδ0 : 0 < δ) (hδ1 : δ < 1) (hv : 0 < v) :
    (∃ P : Profile, IsSPE .R v c δ P) ∧
    (∃ P : Profile, IsSPE .C v c δ P) ∧
    ∀ PR PC : Profile, IsSPE .R v c δ PR → IsSPE .C v c δ PC →
      (v < 2 * Mc c δ * Real.sqrt (1 - δ) / (Zc c δ * Real.sqrt (Fc c δ)) →
        eqCS v δ PR < eqCS v δ PC) ∧
      (2 * Mc c δ * Real.sqrt (1 - δ) / (Zc c δ * Real.sqrt (Fc c δ)) < v →
        eqCS v δ PC < eqCS v δ PR) ∧
      eqProfit v c δ PR < eqProfit v c δ PC ∧
      eqWelfare v c δ PR < eqWelfare v c δ PC := by
  have he : 0 < 1 - δ := by linarith
  have hZ := Z_pos hc hδ0
  have hZne : Zc c δ ≠ 0 := hZ.ne'
  have hK := K_pos hc hδ0 hδ1
  have hKne : Kc c δ ≠ 0 := hK.ne'
  have hM := Mc_pos hc hδ0 hδ1
  have hZ2 : 0 < Zc c δ ^ 2 := by positivity
  have hFpos : 0 < Fc c δ := by
    unfold Fc; nlinarith [mul_pos (mul_pos hc hc) he, mul_pos (mul_pos hc hδ0) he, sq_pos_of_pos hδ0]
  have hb1 : Mc c δ / Zc c δ ^ 2 < 1 := by
    rw [div_lt_one hZ2]; unfold Mc Zc
    nlinarith [mul_pos (mul_pos hc hc) hδ0, mul_pos hc (mul_pos hδ0 hδ0)]
  have hab : 1 - δ < Mc c δ / Zc c δ ^ 2 := by
    rw [lt_div_iff₀ hZ2]; unfold Mc Zc
    nlinarith [mul_pos hc (mul_pos hδ0 hδ0), pow_pos hδ0 3]
  have haf : 1 - δ < Fc c δ / Zc c δ ^ 2 := by
    rw [lt_div_iff₀ hZ2]; unfold Fc Zc
    nlinarith [pow_pos hδ0 3]
  have hfb : Fc c δ / Zc c δ ^ 2 < Mc c δ / Zc c δ ^ 2 := by
    apply div_lt_div_of_pos_right _ hZ2; unfold Fc Mc
    nlinarith [mul_pos hc (mul_pos hδ0 hδ0)]
  have hbpos : 0 < Mc c δ / Zc c δ ^ 2 := by positivity
  have hfpos : 0 < Fc c δ / Zc c δ ^ 2 := by positivity
  have ha1 : 1 - δ < 1 := by linarith
  have hqR : 0 ≤ c * δ ^ 2 / Zc c δ ^ 2 := by positivity
  have hkR : Kc c δ / Zc c δ = Mc c δ / Zc c δ ^ 2 + c * δ ^ 2 / Zc c δ ^ 2 := by
    rw [MZK_id]; field_simp; ring
  -- profit functions
  have hTR : ∀ p (sr : ℝ × ℝ), IsREE .R true v c δ p sr.1 sr.2 →
      firmProfit true v c δ p sr =
        G v (Mc c δ / Zc c δ ^ 2) (Kc c δ / Zc c δ) (c * δ ^ 2 / Zc c δ ^ 2) (yR v c δ p) :=
    fun p sr h => profit_R_true hc hδ0 hδ1 h
  have hFR : ∀ p (sr : ℝ × ℝ), IsREE .R false v c δ p sr.1 sr.2 →
      firmProfit false v c δ p sr = G v 1 1 0 (v - p) := fun p sr h => profit_false h
  have hTC : ∀ p (sr : ℝ × ℝ), IsREE .C true v c δ p sr.1 sr.2 →
      firmProfit true v c δ p sr = G v (1 - δ) (1 - δ) 0 ((v - p) / (1 - δ)) :=
    fun p sr h => profit_C_true hδ0 hδ1 h
  have hFC : ∀ p (sr : ℝ × ℝ), IsREE .C false v c δ p sr.1 sr.2 →
      firmProfit false v c δ p sr = G v 1 1 0 (v - p) := fun p sr h => profit_false h
  have hpsR : yR v c δ (v - Kc c δ * ystar v (Mc c δ / Zc c δ ^ 2) / Zc c δ) =
      ystar v (Mc c δ / Zc c δ ^ 2) := by
    rw [yR, sub_sub_cancel]; field_simp
  have hpsC : (v - (v - (1 - δ) * ystar v (1 - δ))) / (1 - δ) = ystar v (1 - δ) := by
    rw [sub_sub_cancel, mul_div_cancel_left₀ _ he.ne']
  have hyb0 := ystar_pos hv hbpos
  have hyb1 := ystar_le_one (v := v) hbpos
  have hya0 := ystar_pos hv he
  have hya1 := ystar_le_one (v := v) he
  refine ⟨⟨_, spe_exists hv hbpos hb1 hqR hkR hTR hFR hpsR
      (fun ℓ p => if ℓ then (sR v c δ p, rR v c δ p) else (0, 0)) ?_⟩,
    ⟨_, spe_exists hv he ha1 le_rfl (by ring) hTC hFC hpsC
      (fun ℓ p => if ℓ then (discloseQty v δ p 0, 0) else (0, 0)) ?_⟩, ?_⟩
  · intro ℓ p
    cases ℓ
    · simp [IsREE]
    · simp only [↓reduceIte]
      exact (REE_R_iff hc hδ0 hδ1).mpr ⟨rfl, rfl⟩
  · intro ℓ p
    cases ℓ
    · simp [IsREE]
    · simp [IsREE]
  intro PR PC hR hC
  obtain ⟨colR, yRe, profR⟩ := spe_unique hv hbpos hb1 hqR hkR hTR hFR hpsR PR hR
  obtain ⟨colC, yCe, profC⟩ := spe_unique hv he ha1 le_rfl (by ring) hTC hFC hpsC PC hC
  -- consumer surplus
  have csR : eqCS v δ PR =
      Fc c δ / Zc c δ ^ 2 * ystar v (Mc c δ / Zc c δ ^ 2) ^ 2 / 2 := by
    have hREE := hR.1 true (PR.price true)
    rw [REE_R_iff hc hδ0 hδ1] at hREE
    unfold eqCS eqResp eqPrice
    rw [colR, hREE.2, cs_R hc hδ0 hδ1 (by rw [yRe]; exact hyb0.le) (by rw [yRe]; exact hyb1),
      yRe]
  have csC : eqCS v δ PC = (1 - δ) * ystar v (1 - δ) ^ 2 / 2 := by
    have hREE := hC.1 true (PC.price true)
    simp only [IsREE, if_true] at hREE
    unfold eqCS eqResp eqPrice
    rw [colC, hREE.1]
    apply cs_C hδ0 hδ1 hya0.le hya1
    rw [← yCe]; field_simp
  obtain ⟨i1, i2, i3, i4⟩ := final_ineq hv he hab haf hfb
  -- threshold
  have hτpos : 0 < 2 * Mc c δ * Real.sqrt (1 - δ) / (Zc c δ * Real.sqrt (Fc c δ)) := by
    apply div_pos
    · have := Real.sqrt_pos.mpr he; positivity
    · have := Real.sqrt_pos.mpr hFpos; positivity
  have hτ2 : (2 * Mc c δ * Real.sqrt (1 - δ) / (Zc c δ * Real.sqrt (Fc c δ))) ^ 2 =
      4 * (Mc c δ / Zc c δ ^ 2) ^ 2 * (1 - δ) / (Fc c δ / Zc c δ ^ 2) := by
    simp only [div_pow, mul_pow, Real.sq_sqrt he.le, Real.sq_sqrt hFpos.le]
    field_simp
    ring
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro hlt
    rw [csR, csC]; apply i1
    have := pow_lt_pow_left₀ hlt hv.le (by norm_num : (2 : ℕ) ≠ 0)
    rw [hτ2, lt_div_iff₀ hfpos] at this
    linarith
  · intro hlt
    rw [csR, csC]; apply i2
    have := pow_lt_pow_left₀ hlt hτpos.le (by norm_num : (2 : ℕ) ≠ 0)
    rw [hτ2, div_lt_iff₀ hfpos] at this
    linarith
  · rw [profR, profC]; exact i3
  · unfold eqWelfare
    rw [profR, profC, csR, csC]; exact i4


end

end RetailPrivacy.SingleFirm


-- Platform entry point: restates the target verbatim.
namespace RetailPrivacy.SingleFirm

theorem _root_.solution (c δ v : ℝ) (hc : 0 < c) (hδ0 : 0 < δ) (hδ1 : δ < 1) (hv : 0 < v) :
    (∃ P : Profile, IsSPE .R v c δ P) ∧
    (∃ P : Profile, IsSPE .C v c δ P) ∧
    ∀ PR PC : Profile, IsSPE .R v c δ PR → IsSPE .C v c δ PC →
      (v < 2 * Mc c δ * Real.sqrt (1 - δ) / (Zc c δ * Real.sqrt (Fc c δ)) →
        eqCS v δ PR < eqCS v δ PC) ∧
      (2 * Mc c δ * Real.sqrt (1 - δ) / (Zc c δ * Real.sqrt (Fc c δ)) < v →
        eqCS v δ PC < eqCS v δ PR) ∧
      eqProfit v c δ PR < eqProfit v c δ PC ∧
      eqWelfare v c δ PR < eqWelfare v c δ PC := by
  apply @RetailPrivacy.SingleFirm.theorem_1 <;> assumption

end RetailPrivacy.SingleFirm
