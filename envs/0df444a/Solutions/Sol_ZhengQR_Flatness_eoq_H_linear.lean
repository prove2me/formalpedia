-- Prove2me | solution 1 for ZhengQR.Flatness.eoq_H_linear
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-29T03:40:28.296419+00:00
-- url     : https://prove2.me/submissions/3d441f3f-27cd-4b4f-b195-b1ca061b71e9

import Mathlib
import Definitions.Def_ZhengQR_Flatness_QRModel

namespace ZhengQR.Flatness

lemma aux_eoqH_cont (h p lam L : ℝ) : Continuous (eoqCost h p lam L) := by
  unfold eoqCost
  fun_prop

lemma aux_eoqH_nonneg (h p lam L : ℝ) (hh : 0 ≤ h) (hp : 0 ≤ p) (y : ℝ) :
    0 ≤ eoqCost h p lam L y := by
  unfold eoqCost
  have h1 := le_max_right (y - lam * L) 0
  have h2 := le_max_right (lam * L - y) 0
  have := mul_nonneg hh h1
  have := mul_nonneg hp h2
  linarith

lemma aux_eoqH_g (h p a Q t y : ℝ) (hh : 0 < h) (hp : 0 < p) (hQ : 0 < Q)
    (ht : t * (h + p) = h) :
    (a - t * Q < y → 0 < (h * max (y + Q - a) 0 + p * max (a - (y + Q)) 0) -
        (h * max (y - a) 0 + p * max (a - y) 0)) ∧
    (y < a - t * Q → (h * max (y + Q - a) 0 + p * max (a - (y + Q)) 0) -
        (h * max (y - a) 0 + p * max (a - y) 0) < 0) := by
  have hhp : 0 < h + p := add_pos hh hp
  have ht0 : 0 < t := by
    by_contra hc; push Not at hc; nlinarith
  have ht1 : t < 1 := by
    by_contra hc; push Not at hc; nlinarith
  have htQ : t * Q < Q := by nlinarith
  have htQ0 : 0 < t * Q := mul_pos ht0 hQ
  constructor
  · intro hy
    rcases le_or_gt a y with h1 | h1
    · rw [max_eq_left (by linarith : (0:ℝ) ≤ y + Q - a), max_eq_right (by linarith : a - (y + Q) ≤ 0),
        max_eq_left (by linarith : (0:ℝ) ≤ y - a), max_eq_right (by linarith : a - y ≤ 0)]
      nlinarith
    · rw [max_eq_left (by linarith : (0:ℝ) ≤ y + Q - a), max_eq_right (by linarith : a - (y + Q) ≤ 0),
        max_eq_right (by linarith : y - a ≤ 0), max_eq_left (by linarith : (0:ℝ) ≤ a - y)]
      have := mul_pos hhp (by linarith : 0 < y - a + t * Q)
      nlinarith
  · intro hy
    rw [max_eq_right (by linarith : y - a ≤ 0), max_eq_left (by linarith : (0:ℝ) ≤ a - y)]
    rcases le_or_gt (y + Q) a with h1 | h1
    · rw [max_eq_right (by linarith : y + Q - a ≤ 0), max_eq_left (by linarith : (0:ℝ) ≤ a - (y + Q))]
      nlinarith
    · rw [max_eq_left (by linarith : (0:ℝ) ≤ y + Q - a), max_eq_right (by linarith : a - (y + Q) ≤ 0)]
      have := mul_pos hhp (by linarith : 0 < -(y - a + t * Q))
      nlinarith

lemma aux_eoqH_key (M : QRModel) (Q : ℝ) (hQ : 0 < Q) (r : ℝ)
    (hr : r ≠ M.lam * M.L - M.h / (M.h + M.p) * Q) :
    qrCost M.Gd M.lam M.K Q (M.lam * M.L - M.h / (M.h + M.p) * Q) <
      qrCost M.Gd M.lam M.K Q r := by
  obtain ⟨t, ht_def⟩ : ∃ t, t = M.h / (M.h + M.p) := ⟨_, rfl⟩
  rw [← ht_def] at hr ⊢
  obtain ⟨rs, hrs⟩ : ∃ rs, rs = M.lam * M.L - t * Q := ⟨_, rfl⟩
  rw [← hrs] at hr ⊢
  have hhp : 0 < M.h + M.p := add_pos M.h_pos M.p_pos
  have ht : t * (M.h + M.p) = M.h := by rw [ht_def]; field_simp
  have hc : Continuous M.Gd := aux_eoqH_cont _ _ _ _
  have hgc : Continuous (fun y => M.Gd (y + Q) - M.Gd y) :=
    (hc.comp (continuous_add_const Q)).sub hc
  have hF : (∫ y in r..r + Q, M.Gd y) - ∫ y in rs..rs + Q, M.Gd y =
      ∫ y in rs..r, (M.Gd (y + Q) - M.Gd y) := by
    rw [intervalIntegral.integral_interval_sub_interval_comm' (hc.intervalIntegrable _ _)
      (hc.intervalIntegrable _ _) (hc.intervalIntegrable _ _)]
    have hA : IntervalIntegrable (fun y => M.Gd (y + Q)) MeasureTheory.volume rs r :=
      (hc.comp (continuous_add_const Q)).intervalIntegrable _ _
    have hB : IntervalIntegrable (fun y => M.Gd y) MeasureTheory.volume rs r :=
      hc.intervalIntegrable _ _
    rw [intervalIntegral.integral_sub hA hB]
    rw [intervalIntegral.integral_comp_add_right (fun y => M.Gd y)]
  have hpos : 0 < ∫ y in rs..r, (M.Gd (y + Q) - M.Gd y) := by
    rcases lt_or_gt_of_ne hr with h1 | h1
    · rw [intervalIntegral.integral_symm]
      have : 0 < ∫ y in r..rs, -(M.Gd (y + Q) - M.Gd y) := by
        apply intervalIntegral.intervalIntegral_pos_of_pos_on (hgc.neg.intervalIntegrable _ _) _ h1
        intro x hx
        have := (aux_eoqH_g M.h M.p (M.lam * M.L) Q t x M.h_pos M.p_pos hQ ht).2
          (by rw [← hrs]; exact hx.2)
        simp only [Pi.neg_apply, QRModel.Gd, eoqCost]
        linarith
      rw [intervalIntegral.integral_neg] at this
      linarith
    · apply intervalIntegral.intervalIntegral_pos_of_pos_on (hgc.intervalIntegrable _ _) _ h1
      intro x hx
      have := (aux_eoqH_g M.h M.p (M.lam * M.L) Q t x M.h_pos M.p_pos hQ ht).1
        (by rw [← hrs]; exact hx.1)
      simp only [QRModel.Gd, eoqCost]
      linarith
  unfold qrCost
  apply div_lt_div_of_pos_right _ hQ
  linarith

end ZhengQR.Flatness

open ZhengQR.Flatness

theorem solution (M : QRModel) (Q : ℝ) (hQ : 0 ≤ Q) :
    (0 < Q → M.rd Q = M.lam * M.L - M.h / (M.h + M.p) * Q) ∧
      M.Hd Q = M.h * M.p / (M.h + M.p) * Q := by
  have hrd : 0 < Q → M.rd Q = M.lam * M.L - M.h / (M.h + M.p) * Q := by
    intro hQ'
    have hex : ∃ r, IsOptReorder M.Gd M.lam M.K Q r := ⟨_, fun r' => by
      by_cases h : r' = M.lam * M.L - M.h / (M.h + M.p) * Q
      · rw [h]
      · exact (aux_eoqH_key M Q hQ' r' h).le⟩
    have hspec := hex.choose_spec
    unfold QRModel.rd optReorder
    rw [dif_pos hex]
    by_contra hne
    exact absurd (hspec _) (not_le.mpr (aux_eoqH_key M Q hQ' _ hne))
  refine ⟨hrd, ?_⟩
  have hhp : 0 < M.h + M.p := add_pos M.h_pos M.p_pos
  rcases hQ.lt_or_eq with hQ' | hQ'
  · have h1 := hrd hQ'
    unfold QRModel.rd at h1
    unfold QRModel.Hd Hfun
    rw [if_pos hQ', h1]
    simp only [QRModel.Gd, eoqCost]
    have htQ : 0 ≤ M.h / (M.h + M.p) * Q := by
      have := M.h_pos
      positivity
    rw [max_eq_right (by linarith : M.lam * M.L - M.h / (M.h + M.p) * Q - M.lam * M.L ≤ 0),
      max_eq_left (by linarith : (0:ℝ) ≤ M.lam * M.L - (M.lam * M.L - M.h / (M.h + M.p) * Q))]
    field_simp
    ring
  · subst hQ'
    unfold QRModel.Hd Hfun minPoint
    rw [if_neg (lt_irrefl 0)]
    have hGa : M.Gd (M.lam * M.L) = 0 := by
      simp [QRModel.Gd, eoqCost]
    have hex : ∃ y, ∀ z, M.Gd y ≤ M.Gd z := ⟨M.lam * M.L, fun z => by
      rw [hGa]
      exact aux_eoqH_nonneg M.h M.p M.lam M.L M.h_pos.le M.p_pos.le z⟩
    rw [dif_pos hex]
    have h1 := hex.choose_spec (M.lam * M.L)
    have h2 := aux_eoqH_nonneg M.h M.p M.lam M.L M.h_pos.le M.p_pos.le hex.choose
    have h3 : M.Gd hex.choose = 0 := by
      have : M.Gd hex.choose = eoqCost M.h M.p M.lam M.L hex.choose := rfl
      linarith
    rw [h3]
    ring
