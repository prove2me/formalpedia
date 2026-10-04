-- Prove2me | solution 1 for ZhengQR.EOQHeuristic.eoq_model_solution
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-04T06:24:02.076687+00:00
-- url     : https://prove2.me/submissions/b045f788-5cf8-45c6-91b0-63a1743bb04e

import Mathlib
import Definitions.Def_ZhengQR_EOQHeuristic_qrCost
import Definitions.Def_ZhengQR_EOQHeuristic_costCurves
import Definitions.Def_ZhengQR_EOQHeuristic_stochasticModel
open MeasureTheory Filter Topology

set_option autoImplicit false

namespace Dfce1737

open ZhengQR.EOQHeuristic

lemma eoq_cont (lam L h p : ℝ) : Continuous (eoqCost lam L h p) := by
  unfold eoqCost; fun_prop

lemma eoq_nonneg (lam L h p : ℝ) (hh : 0 < h) (hp : 0 < p) (y : ℝ) :
    0 ≤ eoqCost lam L h p y := by
  unfold eoqCost
  exact add_nonneg (mul_nonneg hh.le (le_max_right _ _)) (mul_nonneg hp.le (le_max_right _ _))

lemma int_left (lam L h p a b : ℝ) (hab : a ≤ b) (hb : b ≤ lam * L) :
    ∫ y in a..b, eoqCost lam L h p y = p * ((lam * L - a) ^ 2 - (lam * L - b) ^ 2) / 2 := by
  have e : ∫ y in a..b, eoqCost lam L h p y = ∫ y in a..b, (p * (lam * L) - p * y) := by
    apply intervalIntegral.integral_congr
    intro y hy
    rw [Set.uIcc_of_le hab] at hy
    simp only [eoqCost]
    rw [max_eq_right (by linarith [hy.2]), max_eq_left (by linarith [hy.2])]
    ring
  rw [e, intervalIntegral.integral_sub (by apply Continuous.intervalIntegrable; fun_prop)
    (by apply Continuous.intervalIntegrable; fun_prop), intervalIntegral.integral_const,
    intervalIntegral.integral_const_mul, integral_id]
  simp only [smul_eq_mul]
  ring

lemma int_right (lam L h p a b : ℝ) (hab : a ≤ b) (ha : lam * L ≤ a) :
    ∫ y in a..b, eoqCost lam L h p y = h * ((b - lam * L) ^ 2 - (a - lam * L) ^ 2) / 2 := by
  have e : ∫ y in a..b, eoqCost lam L h p y = ∫ y in a..b, (h * y - h * (lam * L)) := by
    apply intervalIntegral.integral_congr
    intro y hy
    rw [Set.uIcc_of_le hab] at hy
    simp only [eoqCost]
    rw [max_eq_left (by linarith [hy.1]), max_eq_right (by linarith [hy.1])]
    ring
  rw [e, intervalIntegral.integral_sub (by apply Continuous.intervalIntegrable; fun_prop)
    (by apply Continuous.intervalIntegrable; fun_prop), intervalIntegral.integral_const,
    intervalIntegral.integral_const_mul, integral_id]
  simp only [smul_eq_mul]
  ring

/-- Window characterisation. -/
lemma window (lam L h p Q r : ℝ) (hh : 0 < h) (hp : 0 < p) (hQ : 0 < Q) :
    h * p * Q ^ 2 ≤ (h + p) * (2 * ∫ y in r..r + Q, eoqCost lam L h p y) ∧
    ((h + p) * (2 * ∫ y in r..r + Q, eoqCost lam L h p y) ≤ h * p * Q ^ 2 ↔
      (h + p) * (r - lam * L) + h * Q = 0) := by
  rcases le_or_gt (r + Q) (lam * L) with h1 | h1
  · rw [int_left lam L h p r (r + Q) (by linarith) h1]
    have ht : 0 ≤ lam * L - r - Q := by linarith
    have k1 : 0 ≤ 2 * p * Q * (h + p) * (lam * L - r - Q) := by
      have := mul_nonneg (mul_nonneg (mul_nonneg (mul_pos (by norm_num : (0:ℝ) < 2) hp).le hQ.le)
        (add_pos hh hp).le) ht
      linarith
    have k2 : 0 < p * p * (Q * Q) := mul_pos (mul_pos hp hp) (mul_pos hQ hQ)
    have eq : (h + p) * (2 * (p * ((lam * L - r) ^ 2 - (lam * L - (r + Q)) ^ 2) / 2))
        - h * p * Q ^ 2 = 2 * p * Q * (h + p) * (lam * L - r - Q) + p * p * (Q * Q) := by ring
    refine ⟨by linarith, ?_⟩
    constructor
    · intro H; exfalso; linarith
    · intro H; exfalso
      have : (h + p) * (r - lam * L) + h * Q ≤ -(p * Q) := by nlinarith
      nlinarith [mul_pos hp hQ]
  · rcases le_or_gt (lam * L) r with h2 | h2
    · rw [int_right lam L h p r (r + Q) (by linarith) h2]
      have ht : 0 ≤ r - lam * L := by linarith
      have k1 : 0 ≤ 2 * h * Q * (h + p) * (r - lam * L) := by
        have := mul_nonneg (mul_nonneg (mul_nonneg (mul_pos (by norm_num : (0:ℝ) < 2) hh).le hQ.le)
          (add_pos hh hp).le) ht
        linarith
      have k2 : 0 < h * h * (Q * Q) := mul_pos (mul_pos hh hh) (mul_pos hQ hQ)
      have eq : (h + p) * (2 * (h * ((r + Q - lam * L) ^ 2 - (r - lam * L) ^ 2) / 2))
          - h * p * Q ^ 2 = 2 * h * Q * (h + p) * (r - lam * L) + h * h * (Q * Q) := by ring
      refine ⟨by linarith, ?_⟩
      constructor
      · intro H; exfalso; linarith
      · intro H; exfalso
        have : 0 ≤ (h + p) * (r - lam * L) := mul_nonneg (add_pos hh hp).le ht
        nlinarith [mul_pos hh hQ]
    · have hc := eoq_cont lam L h p
      rw [← intervalIntegral.integral_add_adjacent_intervals (b := lam * L)
        (hc.intervalIntegrable _ _) (hc.intervalIntegrable _ _),
        int_left lam L h p r (lam * L) h2.le le_rfl,
        int_right lam L h p (lam * L) (r + Q) h1.le le_rfl]
      have eq : (h + p) * (2 * (p * ((lam * L - r) ^ 2 - (lam * L - lam * L) ^ 2) / 2 +
          h * ((r + Q - lam * L) ^ 2 - (lam * L - lam * L) ^ 2) / 2)) - h * p * Q ^ 2
          = ((h + p) * (r - lam * L) + h * Q) ^ 2 := by ring
      refine ⟨by nlinarith [sq_nonneg ((h + p) * (r - lam * L) + h * Q)], ?_⟩
      constructor
      · intro H
        have h0 : ((h + p) * (r - lam * L) + h * Q) ^ 2 ≤ 0 := by linarith
        have := le_antisymm h0 (sq_nonneg _)
        exact pow_eq_zero_iff (n := 2) (by norm_num) |>.1 this
      · intro H
        rw [H] at eq
        linarith

lemma window_opt_iff (lam L K h p Q r : ℝ) (hQ : 0 < Q) :
    IsOptReorder (eoqCost lam L h p) lam K Q r ↔
      ∀ r', (∫ y in r..r + Q, eoqCost lam L h p y) ≤ ∫ y in r'..r' + Q, eoqCost lam L h p y := by
  unfold IsOptReorder qrCost
  simp only [div_le_div_iff_of_pos_right hQ, add_le_add_iff_left]

lemma reorder_eq (lam L K h p Q : ℝ) (hh : 0 < h) (hp : 0 < p) (hQ : 0 < Q) :
    reorderPt (eoqCost lam L h p) lam K Q = lam * L - h / (h + p) * Q := by
  have hhp : 0 < h + p := add_pos hh hp
  set r0 := lam * L - h / (h + p) * Q with hr0def
  have hr0 : (h + p) * (r0 - lam * L) + h * Q = 0 := by
    rw [hr0def]; field_simp; ring
  have w0 := (window lam L h p Q r0 hh hp hQ).2.mpr hr0
  have hopt : IsOptReorder (eoqCost lam L h p) lam K Q r0 := by
    rw [window_opt_iff _ _ _ _ _ _ _ hQ]
    intro r'
    have w1 := (window lam L h p Q r' hh hp hQ).1
    have : (h + p) * (2 * ∫ y in r0..r0 + Q, eoqCost lam L h p y) ≤
        (h + p) * (2 * ∫ y in r'..r' + Q, eoqCost lam L h p y) := le_trans w0 w1
    have := le_of_mul_le_mul_left this hhp
    linarith
  have hex : ∃ r, IsOptReorder (eoqCost lam L h p) lam K Q r := ⟨r0, hopt⟩
  unfold reorderPt
  rw [dif_pos hex]
  have hs := hex.choose_spec
  rw [window_opt_iff _ _ _ _ _ _ _ hQ] at hs
  have h1 := hs r0
  have h2 : (h + p) * (2 * ∫ y in hex.choose..hex.choose + Q, eoqCost lam L h p y) ≤ h * p * Q ^ 2 := by
    have : (h + p) * (2 * ∫ y in hex.choose..hex.choose + Q, eoqCost lam L h p y) ≤
        (h + p) * (2 * ∫ y in r0..r0 + Q, eoqCost lam L h p y) :=
      mul_le_mul_of_nonneg_left (by linarith) hhp.le
    linarith
  have h3 := (window lam L h p Q hex.choose hh hp hQ).2.mp h2
  have h4 : (h + p) * (hex.choose - r0) = 0 := by linarith
  rcases mul_eq_zero.1 h4 with h5 | h5
  · linarith
  · linarith

lemma window_val (lam L h p Q : ℝ) (hh : 0 < h) (hp : 0 < p) (hQ : 0 < Q) :
    (∫ y in (lam * L - h / (h + p) * Q)..(lam * L - h / (h + p) * Q) + Q, eoqCost lam L h p y)
      = h * p * Q ^ 2 / (2 * (h + p)) := by
  have hhp : 0 < h + p := add_pos hh hp
  have hr0 : (h + p) * ((lam * L - h / (h + p) * Q) - lam * L) + h * Q = 0 := by
    field_simp; ring
  have w := window lam L h p Q (lam * L - h / (h + p) * Q) hh hp hQ
  have e := le_antisymm (w.2.mpr hr0) w.1
  rw [eq_div_iff (by positivity)]
  linarith

lemma optCost_eq (lam L K h p Q : ℝ) (hh : 0 < h) (hp : 0 < p) (hQ : 0 < Q) :
    optCost (eoqCost lam L h p) lam K Q = (lam * K + h * p * Q ^ 2 / (2 * (h + p))) / Q := by
  unfold optCost qrCost
  rw [reorder_eq lam L K h p Q hh hp hQ, window_val lam L h p Q hh hp hQ]

lemma minPt_val (lam L h p : ℝ) (hh : 0 < h) (hp : 0 < p) :
    eoqCost lam L h p (minPt (eoqCost lam L h p)) = 0 := by
  have hm : eoqCost lam L h p (lam * L) = 0 := by simp [eoqCost]
  have hex : ∃ y, ∀ z, eoqCost lam L h p y ≤ eoqCost lam L h p z :=
    ⟨lam * L, fun z => by rw [hm]; exact eoq_nonneg lam L h p hh hp z⟩
  unfold minPt
  rw [dif_pos hex]
  have := hex.choose_spec (lam * L)
  rw [hm] at this
  exact le_antisymm this (eoq_nonneg lam L h p hh hp _)

end Dfce1737

open ZhengQR.EOQHeuristic in
theorem solution {lam L K h p : ℝ} (hlam : 0 < lam) (hL : 0 < L) (hK : 0 < K)
    (hh : 0 < h) (hp : 0 < p) :
    (∀ Q : ℝ, 0 < Q → reorderPt (eoqCost lam L h p) lam K Q = lam * L - h / (h + p) * Q) ∧
    (∀ Q : ℝ, 0 ≤ Q → hFun (eoqCost lam L h p) lam K Q = h * p / (h + p) * Q) ∧
    (∀ Q : ℝ, IsOptQty (eoqCost lam L h p) lam K Q ↔ Q = eoqQty lam K h p) := by
  have hhp : 0 < h + p := add_pos hh hp
  refine ⟨fun Q hQ => Dfce1737.reorder_eq lam L K h p Q hh hp hQ, ?_, ?_⟩
  · intro Q hQ
    rcases hQ.lt_or_eq with hQ | hQ
    · unfold hFun
      rw [if_pos hQ, Dfce1737.reorder_eq lam L K h p Q hh hp hQ]
      unfold eoqCost
      have hpos : 0 < h / (h + p) * Q := by positivity
      have e1 : lam * L - h / (h + p) * Q - lam * L = -(h / (h + p) * Q) := by ring
      have e2 : lam * L - (lam * L - h / (h + p) * Q) = h / (h + p) * Q := by ring
      rw [e1, e2, max_eq_right (by linarith), max_eq_left hpos.le]
      field_simp
      ring
    · subst hQ
      unfold hFun
      rw [if_neg (lt_irrefl 0), Dfce1737.minPt_val lam L h p hh hp]
      ring
  · set Qd := eoqQty lam K h p with hQddef
    have hQd : 0 < Qd := Real.sqrt_pos.2 (by positivity)
    have hQd2 : Qd ^ 2 = 2 * lam * K * (h + p) / (h * p) := Real.sq_sqrt (by positivity)
    have lamK : lam * K = h * p * Qd ^ 2 / (2 * (h + p)) := by
      rw [hQd2]; field_simp
    have key : ∀ Q : ℝ, 0 < Q → optCost (eoqCost lam L h p) lam K Q -
        optCost (eoqCost lam L h p) lam K Qd = h * p / (h + p) * (Q - Qd) ^ 2 / (2 * Q) := by
      intro Q hQ
      rw [Dfce1737.optCost_eq lam L K h p Q hh hp hQ, Dfce1737.optCost_eq lam L K h p Qd hh hp hQd,
        lamK]
      field_simp
      ring
    intro Q
    constructor
    · rintro ⟨hQ, hle⟩
      have h1 := hle Qd hQd
      have h2 := key Q hQ
      have hc : 0 < h * p / (h + p) := by positivity
      have h3 : h * p / (h + p) * (Q - Qd) ^ 2 / (2 * Q) ≤ 0 := by linarith
      have h4 : h * p / (h + p) * (Q - Qd) ^ 2 ≤ 0 := by
        have := (div_le_iff₀ (by positivity : (0:ℝ) < 2 * Q)).1 h3
        linarith
      have h5 : (Q - Qd) ^ 2 ≤ 0 := by
        by_contra hc'
        have hc'' := not_le.mp hc'
        nlinarith [mul_pos hc hc'']
      have := le_antisymm h5 (sq_nonneg _)
      have := pow_eq_zero_iff (n := 2) (by norm_num) |>.1 this
      linarith
    · rintro rfl
      refine ⟨hQd, fun Q' hQ' => ?_⟩
      have h2 := key Q' hQ'
      have : 0 ≤ h * p / (h + p) * (Q' - Qd) ^ 2 / (2 * Q') := by positivity
      linarith
