-- Prove2me | solution 1 for ReactiveCapacity.proposition_2
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-12T05:15:14.588851+00:00
-- url     : https://prove2.me/submissions/309ae895-43e6-42d0-95ec-50ef1cb635f7

import Mathlib
import Definitions.Def_ReactiveCapacity_Model
import Definitions.Def_ReactiveCapacity_Game
import Definitions.Def_ReactiveCapacity_ClosedForms
import Theorems.Thm_ReactiveCapacity_retailer_stage_rule
import Theorems.Thm_ReactiveCapacity_supplier_response_medium
import Theorems.Thm_ReactiveCapacity_supplier_response_high
import Theorems.Thm_ReactiveCapacity_table_B

open ReactiveCapacity

private lemma standing_focus_p2 (P : Params) (hStand : P.Standing) (hFocus : P.Focus) :
    0 < P.θH ∧ 0 < P.αg ∧ P.αb < P.αg ∧ P.αb < 1 ∧ 0 < 1 - P.ρ ∧
    0 < P.ρ * P.αg + 1 - P.ρ ∧ P.θH * P.αb < P.θL * P.αg ∧
    P.θH / P.θL * P.αb - P.αg < 0 ∧ P.ρ * (P.θH - P.θL) < P.θL := by
  rcases hStand with ⟨hθL, hθLH, _hk, hρ0, hρ1, hαb0, hαb_lt, hαg_gt, hαg1⟩
  have hθH : 0 < P.θH := lt_trans hθL hθLH
  have hαg0 : 0 < P.αg := pos_of_mul_pos_left (lt_trans hθL hαg_gt) hθH.le
  have hαb_αg : P.αb < P.αg := lt_of_mul_lt_mul_right (lt_trans hαb_lt hαg_gt) hθH.le
  have hαb1 : P.αb < 1 := lt_trans hαb_αg hαg1
  have h1ρ : 0 < 1 - P.ρ := sub_pos.mpr hρ1
  have hD1 : 0 < P.ρ * P.αg + 1 - P.ρ := by
    have : 0 < P.ρ * P.αg := mul_pos hρ0 hαg0
    linarith
  unfold Params.Focus at hFocus
  have hmix_pos : 0 < (P.ρ * P.θH + (1 - P.ρ) * P.θL) * (P.αg - P.αb) :=
    mul_pos (add_pos (mul_pos hρ0 hθH) (mul_pos h1ρ hθL)) (sub_pos.mpr hαb_αg)
  have hθHab : P.θH * P.αb < P.θL * P.αg := by linarith
  have hcut_neg : P.θH / P.θL * P.αb - P.αg < 0 := by
    have h1 : P.θH / P.θL * P.αb < P.αg := by
      rw [div_mul_eq_mul_div, div_lt_iff₀ hθL]
      linarith
    linarith
  have h1 : 2 * (P.θL * P.αg - P.θH * P.αb) < 2 * P.θL * (P.αg - P.αb) := by
    have : 0 < (P.θH - P.θL) * P.αb := mul_pos (sub_pos.mpr hθLH) hαb0
    linarith
  have h2 : P.ρ * P.θH + (1 - P.ρ) * P.θL < 2 * P.θL :=
    lt_of_mul_lt_mul_right (lt_trans hFocus h1) (sub_pos.mpr hαb_αg).le
  exact ⟨hθH, hαg0, hαb_αg, hαb1, h1ρ, hD1, hθHab, hcut_neg, by linarith⟩

private lemma y_props_p2 (P : Params) (hStand : P.Standing) (hFocus : P.Focus)
    {S : ℝ} (hlo : P.αg ≤ S) (hhi : S ≤ 1) :
    0 < P.ρ * P.αg + (1 - P.ρ) * S ∧ 0 < P.Y S ∧ P.X ≤ P.Y S ∧
    P.Y S < 2 * P.θL ∧ P.Y S * (S - P.αb) < 2 * (P.θL * S - P.θH * P.αb) := by
  obtain ⟨hθH, hαg0, hαb_αg, _, h1ρ, hD1, _, _, hρ_lt⟩ := standing_focus_p2 P hStand hFocus
  rcases hStand with ⟨hθL, hθLH, _, hρ0, _, hαb0, _, _, _⟩
  have hS0 : 0 ≤ S := le_trans hαg0.le hlo
  have hDS : 0 < P.ρ * P.αg + (1 - P.ρ) * S :=
    add_pos_of_pos_of_nonneg (mul_pos hρ0 hαg0) (mul_nonneg h1ρ.le hS0)
  have hYS_pos : 0 < P.Y S := by
    unfold Params.Y
    exact div_pos (add_pos (mul_pos (mul_pos hρ0 hαg0) hθH)
      (mul_pos (mul_pos h1ρ (lt_of_lt_of_le hαg0 hlo)) hθL)) hDS
  have hX_le : P.X ≤ P.Y S := by
    unfold Params.X Params.Y
    have hD1' : 0 < P.ρ * P.αg + (1 - P.ρ) * 1 := by linarith
    rw [div_le_div_iff₀ hD1' hDS]
    have hdiff :
        (P.ρ * P.αg * P.θH + (1 - P.ρ) * S * P.θL) * (P.ρ * P.αg + (1 - P.ρ) * 1) -
          (P.ρ * P.αg * P.θH + (1 - P.ρ) * 1 * P.θL) * (P.ρ * P.αg + (1 - P.ρ) * S) =
          P.ρ * P.αg * (1 - P.ρ) * (P.θH - P.θL) * (1 - S) := by ring
    have hnn : 0 ≤ P.ρ * P.αg * (1 - P.ρ) * (P.θH - P.θL) * (1 - S) :=
      mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hρ0.le hαg0.le) h1ρ.le)
        (sub_pos.mpr hθLH).le) (sub_nonneg.mpr hhi)
    linarith
  have hYS_le_Y0 : P.Y S ≤ P.ρ * P.θH + (1 - P.ρ) * P.θL := by
    unfold Params.Y
    rw [div_le_iff₀ hDS]
    have hdiff :
        (P.ρ * P.θH + (1 - P.ρ) * P.θL) * (P.ρ * P.αg + (1 - P.ρ) * S) -
          (P.ρ * P.αg * P.θH + (1 - P.ρ) * S * P.θL) =
          P.ρ * (1 - P.ρ) * (P.θH - P.θL) * (S - P.αg) := by ring
    have hnn : 0 ≤ P.ρ * (1 - P.ρ) * (P.θH - P.θL) * (S - P.αg) :=
      mul_nonneg (mul_nonneg (mul_nonneg hρ0.le h1ρ.le) (sub_pos.mpr hθLH).le)
        (sub_nonneg.mpr hlo)
    linarith
  have hYS_lt : P.Y S < 2 * P.θL := by linarith
  have hSab : 0 < S - P.αb := by linarith
  have hYS_f : P.Y S * (S - P.αb) < 2 * (P.θL * S - P.θH * P.αb) := by
    unfold Params.Focus at hFocus
    have h1 : P.Y S * (S - P.αb) * (P.αg - P.αb) ≤
        (P.ρ * P.θH + (1 - P.ρ) * P.θL) * (P.αg - P.αb) * (S - P.αb) := by
      have := mul_le_mul_of_nonneg_right hYS_le_Y0
        (mul_nonneg hSab.le (sub_pos.mpr hαb_αg).le)
      linarith
    have h2 : (P.ρ * P.θH + (1 - P.ρ) * P.θL) * (P.αg - P.αb) * (S - P.αb) <
        2 * (P.θL * P.αg - P.θH * P.αb) * (S - P.αb) :=
      mul_lt_mul_of_pos_right hFocus hSab
    have h3 : 2 * (P.θL * P.αg - P.θH * P.αb) * (S - P.αb) ≤
        2 * (P.θL * S - P.θH * P.αb) * (P.αg - P.αb) := by
      have : 0 ≤ 2 * (P.θH - P.θL) * P.αb * (S - P.αg) :=
        mul_nonneg (mul_nonneg (by linarith) hαb0.le) (sub_nonneg.mpr hlo)
      linarith
    exact lt_of_mul_lt_mul_right (lt_of_le_of_lt h1 (lt_of_lt_of_le h2 h3))
      (sub_pos.mpr hαb_αg).le
  exact ⟨hDS, hYS_pos, hX_le, hYS_lt, hYS_f⟩

private lemma vos_mono_p2 (P : Params) (hStand : P.Standing) (hFocus : P.Focus)
    {Q₁ Q₂ : ℝ} (h0 : 0 ≤ Q₁) (hle : Q₁ ≤ Q₂) :
    P.V_OS Q₁ ≤ P.V_OS Q₂ := by
  obtain ⟨_, hαg0, _, _, h1ρ, _, _, _, hρ_lt⟩ := standing_focus_p2 P hStand hFocus
  rcases hStand with ⟨hθL, hθLH, hk, hρ0, _, _, _, _, hαg1⟩
  let S₁ := P.supplyS Q₁
  let S₂ := P.supplyS Q₂
  have hS₁_lo : P.αg ≤ S₁ := le_min (by linarith) hαg1.le
  have hS₁_le_S₂ : S₁ ≤ S₂ := min_le_min_right 1 (by linarith)
  rcases eq_or_lt_of_le hS₁_le_S₂ with hSeq | hSlt
  · unfold Params.V_OS
    change (P.ρ * P.αg + (1 - P.ρ) * S₁) * P.Y S₁ ^ 2 / (4 * P.k) ≤
      (P.ρ * P.αg + (1 - P.ρ) * S₂) * P.Y S₂ ^ 2 / (4 * P.k)
    rw [hSeq]
  · let C := P.ρ * P.αg * (P.θH - P.θL)
    have hC_pos : 0 < C := mul_pos (mul_pos hρ0 hαg0) (sub_pos.mpr hθLH)
    have hC_lt : C < P.αg * P.θL := by
      dsimp [C]; have := mul_lt_mul_of_pos_right hρ_lt hαg0; linarith
    let u₁ := P.ρ * P.αg + (1 - P.ρ) * S₁
    let u₂ := P.ρ * P.αg + (1 - P.ρ) * S₂
    have hu₁_ge : P.αg ≤ u₁ := by
      have := mul_le_mul_of_nonneg_left hS₁_lo h1ρ.le; dsimp [u₁]; linarith
    have hu₁_pos : 0 < u₁ := lt_of_lt_of_le hαg0 hu₁_ge
    have hu₁_lt_u₂ : u₁ < u₂ := by
      have := mul_lt_mul_of_pos_left hSlt h1ρ; dsimp [u₁, u₂]; linarith
    have hu₂_pos : 0 < u₂ := lt_trans hu₁_pos hu₁_lt_u₂
    have hV₁ : P.V_OS Q₁ = (C + u₁ * P.θL) ^ 2 / (u₁ * (4 * P.k)) := by
      unfold Params.V_OS Params.Y
      change u₁ * ((P.ρ * P.αg * P.θH + (1 - P.ρ) * S₁ * P.θL) / u₁) ^ 2 / (4 * P.k) = _
      have hnum : P.ρ * P.αg * P.θH + (1 - P.ρ) * S₁ * P.θL = C + u₁ * P.θL := by
        dsimp [C, u₁]; ring
      rw [hnum]; field_simp [hu₁_pos.ne', hk.ne']
    have hV₂ : P.V_OS Q₂ = (C + u₂ * P.θL) ^ 2 / (u₂ * (4 * P.k)) := by
      unfold Params.V_OS Params.Y
      change u₂ * ((P.ρ * P.αg * P.θH + (1 - P.ρ) * S₂ * P.θL) / u₂) ^ 2 / (4 * P.k) = _
      have hnum : P.ρ * P.αg * P.θH + (1 - P.ρ) * S₂ * P.θL = C + u₂ * P.θL := by
        dsimp [C, u₂]; ring
      rw [hnum]; field_simp [hu₂_pos.ne', hk.ne']
    rw [hV₁, hV₂, div_le_div_iff₀ (mul_pos hu₁_pos (by linarith)) (mul_pos hu₂_pos (by linarith))]
    have hC1 : C < u₁ * P.θL := lt_of_lt_of_le hC_lt (mul_le_mul_of_nonneg_right hu₁_ge hθL.le)
    have hC2 : C < u₂ * P.θL := lt_trans hC1 (mul_lt_mul_of_pos_right hu₁_lt_u₂ hθL)
    have hCsq : C ^ 2 < u₁ * u₂ * P.θL ^ 2 := by
      have := mul_lt_mul'' hC1 hC2 hC_pos.le hC_pos.le
      linarith [show (u₁ * P.θL) * (u₂ * P.θL) = u₁ * u₂ * P.θL ^ 2 by ring]
    have hid :
        (C + u₂ * P.θL) ^ 2 * (u₁ * (4 * P.k)) - (C + u₁ * P.θL) ^ 2 * (u₂ * (4 * P.k)) =
          4 * P.k * (u₂ - u₁) * (u₁ * u₂ * P.θL ^ 2 - C ^ 2) := by ring
    have hpos : 0 < 4 * P.k * (u₂ - u₁) * (u₁ * u₂ * P.θL ^ 2 - C ^ 2) :=
      mul_pos (mul_pos (by linarith) (sub_pos.mpr hu₁_lt_u₂)) (sub_pos.mpr hCsq)
    linarith

private lemma vos_top_eq_p2 (P : Params) {Q : ℝ} (h : 1 - P.αg ≤ Q) :
    P.V_OS Q = (P.ρ * P.αg + 1 - P.ρ) * P.X ^ 2 / (4 * P.k) := by
  have hS : P.supplyS Q = 1 := min_eq_right (by linarith)
  unfold Params.V_OS Params.X
  rw [hS]
  ring

private lemma voo_lt_vos_top_p2 (P : Params) (hStand : P.Standing) (hFocus : P.Focus) :
    P.V_OO < P.V_OS (1 - P.αg) := by
  obtain ⟨_, _, _, _, _, hD1, _, _, _⟩ := standing_focus_p2 P hStand hFocus
  obtain ⟨_, hX_pos, _, _, _⟩ := y_props_p2 P hStand hFocus hStand.2.2.2.2.2.2.2.2.le (le_refl 1)
  rcases hStand with ⟨_, _, hk, hρ0, _, _, _, _, _⟩
  rw [vos_top_eq_p2 P (le_refl _)]
  unfold Params.V_OO
  refine div_lt_div_of_pos_right ?_ (by linarith)
  have : 0 < P.ρ * (P.ρ * P.αg + 1 - P.ρ) * P.X ^ 2 :=
    mul_pos (mul_pos hρ0 hD1) (pow_pos hX_pos 2)
  linarith

private lemma ho_over_lt_vos0_p2 (P : Params) (hStand : P.Standing) (hFocus : P.Focus) :
    (P.ρ * P.αg + (1 - P.ρ) * P.αb) * P.ρ * P.θH ^ 2 / (4 * P.k) < P.V_OS 0 := by
  obtain ⟨hθH, hαg0, _, _, h1ρ, _, hθHab, _, _⟩ := standing_focus_p2 P hStand hFocus
  rcases hStand with ⟨hθL, _, hk, hρ0, _, _, _, _, hαg1⟩
  have hS0 : P.supplyS 0 = P.αg := by unfold Params.supplyS; rw [add_zero]; exact min_eq_left hαg1.le
  have hY0 : P.Y P.αg = P.ρ * P.θH + (1 - P.ρ) * P.θL := by
    unfold Params.Y; field_simp [hαg0.ne']; ring
  unfold Params.V_OS
  rw [hS0, hY0]
  have hden : P.ρ * P.αg + (1 - P.ρ) * P.αg = P.αg := by ring
  rw [hden]
  refine div_lt_div_of_pos_right ?_ (by linarith)
  have hid :
      P.αg * (P.ρ * P.θH + (1 - P.ρ) * P.θL) ^ 2 -
        (P.ρ * P.αg + (1 - P.ρ) * P.αb) * P.ρ * P.θH ^ 2 =
        P.ρ * (1 - P.ρ) * P.θH * (2 * P.θL * P.αg - P.θH * P.αb) +
          P.αg * (1 - P.ρ) ^ 2 * P.θL ^ 2 := by ring
  have h1 : 0 < 2 * P.θL * P.αg - P.θH * P.αb := by
    have : 0 < P.θL * P.αg := mul_pos hθL hαg0
    linarith
  have h2 : 0 < P.ρ * (1 - P.ρ) * P.θH * (2 * P.θL * P.αg - P.θH * P.αb) :=
    mul_pos (mul_pos (mul_pos hρ0 h1ρ) hθH) h1
  have h3 : 0 < P.αg * (1 - P.ρ) ^ 2 * P.θL ^ 2 :=
    mul_pos (mul_pos hαg0 (pow_pos h1ρ 2)) (pow_pos hθL 2)
  linarith

private lemma vos_continuousOn_p2 (P : Params) (hStand : P.Standing) (hFocus : P.Focus) :
    ContinuousOn P.V_OS (Set.Icc 0 (1 - P.αg)) := by
  obtain ⟨_, hαg0, _, _, h1ρ, _, _, _, _⟩ := standing_focus_p2 P hStand hFocus
  rcases hStand with ⟨_, _, hk, hρ0, _, _, _, _, _⟩
  have hsupp : Continuous P.supplyS := (continuous_const.add continuous_id).min continuous_const
  have hden_ne : ∀ Q ∈ Set.Icc 0 (1 - P.αg), P.ρ * P.αg + (1 - P.ρ) * P.supplyS Q ≠ 0 := by
    intro Q hQ
    have hS0 : 0 ≤ P.supplyS Q := le_min (by linarith [hQ.1]) zero_le_one
    exact (add_pos_of_pos_of_nonneg (mul_pos hρ0 hαg0) (mul_nonneg h1ρ.le hS0)).ne'
  have hnum_c : Continuous (fun Q => P.ρ * P.αg * P.θH + (1 - P.ρ) * P.supplyS Q * P.θL) :=
    continuous_const.add ((continuous_const.mul hsupp).mul continuous_const)
  have hden_c : Continuous (fun Q => P.ρ * P.αg + (1 - P.ρ) * P.supplyS Q) :=
    continuous_const.add (continuous_const.mul hsupp)
  have hY_c : ContinuousOn (fun Q => P.Y (P.supplyS Q)) (Set.Icc 0 (1 - P.αg)) :=
    hnum_c.continuousOn.div hden_c.continuousOn hden_ne
  exact ((hden_c.continuousOn.mul (hY_c.pow 2)).div_const (4 * P.k))

private lemma ub_quad_os_p2 (P : Params) {S q w : ℝ} (hk : 0 < P.k)
    (hDS : 0 < P.ρ * P.αg + (1 - P.ρ) * S) :
    P.ρ * ((q * P.θH - w) * P.αg) + (1 - P.ρ) * ((q * P.θL - w) * S) =
      (P.ρ * P.αg + (1 - P.ρ) * S) * P.Y S ^ 2 / (4 * P.k) -
        (P.ρ * P.αg + (1 - P.ρ) * S) * P.k * (q - P.Y S / (2 * P.k)) ^ 2 -
        (P.ρ * P.αg + (1 - P.ρ) * S) * (w - P.cost q) := by
  unfold Params.Y Params.cost
  field_simp [hDS.ne', hk.ne']
  ring

private lemma ub_quad_oo_p2 (P : Params) {q w : ℝ} (hk : 0 < P.k) (h1ρ : 0 < 1 - P.ρ)
    (hD1 : 0 < P.ρ * P.αg + 1 - P.ρ) (hw_ge : P.cost q / (1 - P.ρ) ≤ w) :
    P.ρ * ((q * P.θH - w) * P.αg) + (1 - P.ρ) * (q * P.θL - w) ≤ P.V_OO := by
  have hid :
      P.ρ * ((q * P.θH - P.cost q / (1 - P.ρ)) * P.αg) +
        (1 - P.ρ) * (q * P.θL - P.cost q / (1 - P.ρ)) =
        P.V_OO - (P.ρ * P.αg + 1 - P.ρ) / (1 - P.ρ) * P.k *
          (q - (1 - P.ρ) * P.X / (2 * P.k)) ^ 2 := by
    unfold Params.V_OO Params.X Params.Y Params.cost
    have hd : P.ρ * P.αg + (1 - P.ρ) * 1 = P.ρ * P.αg + 1 - P.ρ := by ring
    rw [hd]
    field_simp [hk.ne', h1ρ.ne', hD1.ne']
    ring
  have h1 : P.ρ * ((q * P.θH - w) * P.αg) + (1 - P.ρ) * (q * P.θL - w) ≤
      P.ρ * ((q * P.θH - P.cost q / (1 - P.ρ)) * P.αg) +
        (1 - P.ρ) * (q * P.θL - P.cost q / (1 - P.ρ)) := by
    have := mul_le_mul_of_nonneg_left (sub_nonneg.mpr hw_ge) hD1.le
    linarith
  have hsq : 0 ≤ (P.ρ * P.αg + 1 - P.ρ) / (1 - P.ρ) * P.k *
      (q - (1 - P.ρ) * P.X / (2 * P.k)) ^ 2 :=
    mul_nonneg (mul_nonneg (div_nonneg hD1.le h1ρ.le) hk.le) (sq_nonneg _)
  linarith

private lemma tie_gap_p2 (P : Params) (hStand : P.Standing) (hFocus : P.Focus) :
    ∃ gap : ℝ, 0 < gap ∧
      ∀ q w S₀ : ℝ, 0 < q → P.cost q ≤ w → P.αg ≤ S₀ → S₀ ≤ 1 →
        (q * P.θH - w) * P.αb = (q * P.θL - w) * S₀ →
        P.ρ * ((q * P.θH - w) * P.αg) + (1 - P.ρ) * ((q * P.θL - w) * S₀) ≤
          P.V_OS (1 - P.αg) - gap := by
  obtain ⟨_, hαg0, hαb_αg, _, h1ρ, hD1, _, _, _⟩ := standing_focus_p2 P hStand hFocus
  obtain ⟨_, hY0_pos, hX_le_Y0, _, hY0_f⟩ :=
    y_props_p2 P hStand hFocus (le_refl P.αg) hStand.2.2.2.2.2.2.2.2.le
  obtain ⟨_, hX_pos, _, _, _⟩ :=
    y_props_p2 P hStand hFocus hStand.2.2.2.2.2.2.2.2.le (le_refl 1)
  have hX_pos' : 0 < P.X := hX_pos
  rcases hStand with ⟨_, hθLH, hk, hρ0, _, hαb0, _, _, _⟩
  let w₀ := (P.θL * P.αg - P.θH * P.αb) / (P.αg - P.αb)
  have hw₀_gt : P.X / 2 < w₀ := by
    dsimp [w₀]
    rw [div_lt_div_iff₀ (by norm_num : (0 : ℝ) < 2) (sub_pos.mpr hαb_αg)]
    have := mul_le_mul_of_nonneg_right hX_le_Y0 (sub_pos.mpr hαb_αg).le
    linarith
  let δ := w₀ - P.X / 2
  have hδ_pos : 0 < δ := sub_pos.mpr hw₀_gt
  let g₁ := P.k * (P.X / (4 * P.k)) ^ 2
  let g₂ := P.k * (δ / (2 * P.k)) ^ 2
  let g₃ := P.X / (4 * P.k) * (δ / 2)
  have hg₁ : 0 < g₁ := mul_pos hk (pow_pos (div_pos hX_pos' (by linarith)) 2)
  have hg₂ : 0 < g₂ := mul_pos hk (pow_pos (div_pos hδ_pos (by linarith)) 2)
  have hg₃ : 0 < g₃ := mul_pos (div_pos hX_pos' (by linarith)) (half_pos hδ_pos)
  let m := min (min g₁ g₂) g₃
  have hm_pos : 0 < m := lt_min (lt_min hg₁ hg₂) hg₃
  refine ⟨(P.ρ * P.αg + 1 - P.ρ) * m, mul_pos hD1 hm_pos, ?_⟩
  intro q w S₀ hq hcw hS₀_lo hS₀_hi htie
  have hSab : 0 < S₀ - P.αb := by linarith
  have hw_Sab : w * (S₀ - P.αb) = q * (P.θL * S₀ - P.θH * P.αb) := by linarith
  have hwL_Sab : (q * P.θL - w) * (S₀ - P.αb) = q * (P.θH - P.θL) * P.αb := by linarith
  have hwL_pos : 0 < q * P.θL - w :=
    pos_of_mul_pos_left (by rw [hwL_Sab]; exact mul_pos (mul_pos hq (sub_pos.mpr hθLH)) hαb0) hSab.le
  have hqw₀_le : q * w₀ ≤ w := by
    change q * ((P.θL * P.αg - P.θH * P.αb) / (P.αg - P.αb)) ≤ w
    rw [← mul_div_assoc, div_le_iff₀ (sub_pos.mpr hαb_αg)]
    have hstep : q * (P.θL * P.αg - P.θH * P.αb) * (S₀ - P.αb) ≤
        q * (P.θL * S₀ - P.θH * P.αb) * (P.αg - P.αb) := by
      have : 0 ≤ q * (P.θH - P.θL) * P.αb * (S₀ - P.αg) :=
        mul_nonneg (mul_nonneg (mul_nonneg hq.le (sub_pos.mpr hθLH).le) hαb0.le)
          (sub_nonneg.mpr hS₀_lo)
      linarith
    have hw_mul : w * (P.αg - P.αb) * (S₀ - P.αb) =
        q * (P.θL * S₀ - P.θH * P.αb) * (P.αg - P.αb) := by
      calc w * (P.αg - P.αb) * (S₀ - P.αb) = w * (S₀ - P.αb) * (P.αg - P.αb) := by ring
        _ = q * (P.θL * S₀ - P.θH * P.αb) * (P.αg - P.αb) := by rw [hw_Sab]
    exact le_of_mul_le_mul_right (by linarith) hSab
  have hub1 : P.ρ * ((q * P.θH - w) * P.αg) + (1 - P.ρ) * ((q * P.θL - w) * S₀) ≤
      P.ρ * ((q * P.θH - w) * P.αg) + (1 - P.ρ) * ((q * P.θL - w) * 1) := by
    have h1 : (q * P.θL - w) * S₀ ≤ (q * P.θL - w) * 1 :=
      mul_le_mul_of_nonneg_left hS₀_hi hwL_pos.le
    have := mul_le_mul_of_nonneg_left h1 h1ρ.le
    linarith
  have hquad := ub_quad_os_p2 P (S := 1) (q := q) (w := w) hk (by linarith)
  have htop_eq : (P.ρ * P.αg + (1 - P.ρ) * 1) * P.Y 1 ^ 2 / (4 * P.k) = P.V_OS (1 - P.αg) := by
    rw [vos_top_eq_p2 P (le_refl _)]; unfold Params.X; ring
  have hpen_ge : m ≤ P.k * (q - P.X / (2 * P.k)) ^ 2 + (w - P.cost q) := by
    rcases le_or_gt q (P.X / (4 * P.k)) with hq_sm | hq_gt
    · have hdiff : P.X / (4 * P.k) ≤ P.X / (2 * P.k) - q := by
        linarith [show P.X / (2 * P.k) = 2 * (P.X / (4 * P.k)) by ring]
      have hsq : (P.X / (4 * P.k)) ^ 2 ≤ (q - P.X / (2 * P.k)) ^ 2 := by
        have := pow_le_pow_left₀ (div_pos hX_pos' (by linarith)).le hdiff 2
        linarith [show (P.X / (2 * P.k) - q) ^ 2 = (q - P.X / (2 * P.k)) ^ 2 by ring]
      have h1 : m ≤ g₁ := le_trans (min_le_left _ _) (min_le_left _ _)
      have h2 : g₁ ≤ P.k * (q - P.X / (2 * P.k)) ^ 2 := mul_le_mul_of_nonneg_left hsq hk.le
      linarith [sub_nonneg.mpr hcw]
    · rcases le_or_gt (P.X / (2 * P.k) + δ / (2 * P.k)) q with hq_lg | hq_mid
      · have hdiff : δ / (2 * P.k) ≤ q - P.X / (2 * P.k) := by linarith
        have hsq : (δ / (2 * P.k)) ^ 2 ≤ (q - P.X / (2 * P.k)) ^ 2 :=
          pow_le_pow_left₀ (div_pos hδ_pos (by linarith)).le hdiff 2
        have h1 : m ≤ g₂ := le_trans (min_le_left _ _) (min_le_right _ _)
        have h2 : g₂ ≤ P.k * (q - P.X / (2 * P.k)) ^ 2 := mul_le_mul_of_nonneg_left hsq hk.le
        linarith [sub_nonneg.mpr hcw]
      · have hkq_lt : P.k * q < P.X / 2 + δ / 2 := by
          have h1 : P.k * q < P.k * (P.X / (2 * P.k) + δ / (2 * P.k)) :=
            mul_lt_mul_of_pos_left hq_mid hk
          have h2 : P.k * (P.X / (2 * P.k) + δ / (2 * P.k)) = P.X / 2 + δ / 2 := by
            field_simp [hk.ne']
          linarith
        have hwc_ge : g₃ ≤ w - P.cost q := by
          unfold Params.cost
          have h1 : q * (P.X / 2 + δ) ≤ w := by dsimp [δ] at *; linarith
          have h2 : P.k * q ^ 2 ≤ q * (P.X / 2 + δ / 2) := by
            have := mul_le_mul_of_nonneg_left hkq_lt.le hq.le
            linarith [show q * (P.k * q) = P.k * q ^ 2 by ring]
          have h3 : g₃ ≤ q * (δ / 2) := mul_le_mul_of_nonneg_right hq_gt.le (half_pos hδ_pos).le
          linarith
        have h1 : m ≤ g₃ := min_le_right _ _
        have hsq0 : 0 ≤ P.k * (q - P.X / (2 * P.k)) ^ 2 := mul_nonneg hk.le (sq_nonneg _)
        linarith
  have hmul_pen := mul_le_mul_of_nonneg_left hpen_ge hD1.le
  unfold Params.X at hmul_pen
  have hd : P.ρ * P.αg + (1 - P.ρ) * 1 = P.ρ * P.αg + 1 - P.ρ := by ring
  rw [hd] at hquad htop_eq
  linarith

private lemma sv0_nonneg_p2 (P : Params) (hStand : P.Standing) {Qbar : ℝ} (hQ0 : 0 ≤ Qbar)
    (σ : Profile) (hpost : IsPostInventorySPE P Qbar σ) {q w : ℝ} (hq : 0 ≤ q) (hw : 0 ≤ w) :
    0 ≤ σ.supplierValue P q w 0 := by
  rcases hStand with ⟨_, _, _, hρ0, hρ1, _, _, _, _⟩
  have hst : ∀ s : State, 0 ≤ σ.supplierStateValue P q w 0 s := by
    intro s
    obtain ⟨hQs0, _⟩ := hpost.2.2 q w 0 s hq hw (le_refl 0)
    unfold Profile.supplierStateValue Params.supplierState Profile.recv Profile.made
      received inSeason
    rcases le_or_gt (σ.order q w 0 s) 0 with hle | hgt
    · simp [le_antisymm hle hQs0]
    · have hropt := (hpost.2.1 q w 0 s (σ.order q w 0 s) hq hw (le_refl 0) hgt).2.2
        0 (le_refl 0) hQ0
      unfold Params.supplierState received at hropt
      simp only [if_neg (not_le_of_gt hgt), zero_add, min_eq_left hQs0, mul_zero, sub_zero] at hropt
      simp only [if_neg (not_le_of_gt hgt), zero_add]
      linarith
  unfold Profile.supplierValue Params.prob
  exact add_nonneg (mul_nonneg hρ0.le (hst .good)) (mul_nonneg (sub_pos.mpr hρ1).le (hst .bad))

private lemma w_le_cost_props_p2 (P : Params) (hStand : P.Standing) {Qbar : ℝ} (hQ0 : 0 ≤ Qbar)
    (σ : Profile) (hpost : IsPostInventorySPE P Qbar σ)
    {q w I : ℝ} (hq : 0 ≤ q) (hw : 0 ≤ w) (hI0 : 0 ≤ I)
    (hsv_nn : 0 ≤ σ.supplierValue P q w I) (hw_le : w ≤ P.cost q) :
    σ.supplierValue P q w I = 0 ∧
      (w = P.cost q → 0 < q →
        I ≤ σ.recv q w I .good (σ.order q w I .good) ∧
        I ≤ σ.recv q w I .bad (σ.order q w I .bad)) := by
  rcases hStand with ⟨_, _, hk, hρ0, hρ1, _, _, _, _⟩
  have h1ρ : 0 < 1 - P.ρ := sub_pos.mpr hρ1
  have hc0 : 0 ≤ P.cost q := mul_nonneg hk.le (sq_nonneg q)
  have hst : ∀ s : State, σ.supplierStateValue P q w I s ≤ 0 ∧
      (w = P.cost q → 0 < q → σ.recv q w I s (σ.order q w I s) < I →
        σ.supplierStateValue P q w I s < 0) := by
    intro s
    unfold Profile.supplierStateValue Params.supplierState Profile.recv Profile.made
      received inSeason
    rcases le_or_gt (σ.order q w I s) I with hQI | hIQ
    · rw [if_pos hQI, if_pos hQI, add_zero]
      refine ⟨?_, fun hwc hqp hlt => ?_⟩
      · obtain ⟨hQs0, _⟩ := hpost.2.2 q w I s hq hw hI0
        have h1 : w * σ.order q w I s ≤ P.cost q * σ.order q w I s :=
          mul_le_mul_of_nonneg_right hw_le hQs0
        have h2 : P.cost q * σ.order q w I s ≤ P.cost q * I :=
          mul_le_mul_of_nonneg_left hQI hc0
        linarith
      · have hw_mul : w * σ.order q w I s = P.cost q * σ.order q w I s := by rw [hwc]
        have hc_pos : 0 < P.cost q := mul_pos hk (pow_pos hqp 2)
        have := mul_lt_mul_of_pos_left hlt hc_pos
        linarith
    · obtain ⟨hr0, _, hropt_fn⟩ := hpost.2.1 q w I s (σ.order q w I s) hq hw hI0 hIQ
      have hropt := hropt_fn 0 (le_refl 0) hQ0
      unfold Params.supplierState received at hropt
      simp only [if_neg (not_le_of_gt hIQ), add_zero, min_eq_left hIQ.le] at hropt
      simp only [if_neg (not_le_of_gt hIQ)]
      have h0 : w * I - P.cost q * I ≤ 0 := by
        have := mul_le_mul_of_nonneg_right hw_le hI0; linarith
      rcases lt_or_eq_of_le hw_le with hw_lt | hwc
      · -- w < cost q forces react = 0, else hropt fails
        have hle_tot : w * min (I + σ.react q w I s (σ.order q w I s)) (σ.order q w I s) -
            P.cost q * (I + σ.react q w I s (σ.order q w I s)) ≤ 0 := by
          have hm0 : 0 ≤ min (I + σ.react q w I s (σ.order q w I s)) (σ.order q w I s) :=
            le_min (add_nonneg hI0 hr0) (lt_of_le_of_lt hI0 hIQ).le
          have h1 : w * min (I + σ.react q w I s (σ.order q w I s)) (σ.order q w I s) ≤
              P.cost q * min (I + σ.react q w I s (σ.order q w I s)) (σ.order q w I s) :=
            mul_le_mul_of_nonneg_right hw_lt.le hm0
          have h2 : P.cost q * min (I + σ.react q w I s (σ.order q w I s)) (σ.order q w I s) ≤
              P.cost q * (I + σ.react q w I s (σ.order q w I s)) :=
            mul_le_mul_of_nonneg_left (min_le_left _ _) hc0
          linarith
        exact ⟨hle_tot, fun heq => absurd heq hw_lt.ne⟩
      · refine ⟨?_, fun _ hqp hlt => ?_⟩
        · have hw_mul : w * min (I + σ.react q w I s (σ.order q w I s)) (σ.order q w I s) =
              P.cost q * min (I + σ.react q w I s (σ.order q w I s)) (σ.order q w I s) := by
            rw [hwc]
          have := mul_le_mul_of_nonneg_left
            (min_le_left (I + σ.react q w I s (σ.order q w I s)) (σ.order q w I s)) hc0
          linarith
        · have hc_pos : 0 < P.cost q := mul_pos hk (pow_pos hqp 2)
          have hII_le : I + σ.react q w I s (σ.order q w I s) ≤ σ.order q w I s := by
            by_contra hc
            have hgt : σ.order q w I s < I + σ.react q w I s (σ.order q w I s) := lt_of_not_ge hc
            rw [min_eq_right hgt.le] at hropt
            have hw_mul : w * σ.order q w I s = P.cost q * σ.order q w I s := by rw [hwc]
            have hw_I : w * I = P.cost q * I := by rw [hwc]
            have := mul_lt_mul_of_pos_left hgt hc_pos
            linarith
          rw [min_eq_left hII_le] at hlt
          linarith
  have hsv_eq0 : σ.supplierValue P q w I = 0 := by
    unfold Profile.supplierValue Params.prob at hsv_nn ⊢
    have := mul_nonpos_of_nonneg_of_nonpos hρ0.le (hst .good).1
    have := mul_nonpos_of_nonneg_of_nonpos h1ρ.le (hst .bad).1
    linarith
  refine ⟨hsv_eq0, fun hwc hqp => ⟨?_, ?_⟩⟩
  · by_contra hc
    have hlt := (hst .good).2 hwc hqp (lt_of_not_ge hc)
    unfold Profile.supplierValue Params.prob at hsv_nn
    have := mul_lt_mul_of_pos_left hlt hρ0
    have := mul_nonpos_of_nonneg_of_nonpos h1ρ.le (hst .bad).1
    linarith
  · by_contra hc
    have hlt := (hst .bad).2 hwc hqp (lt_of_not_ge hc)
    unfold Profile.supplierValue Params.prob at hsv_nn
    have := mul_nonpos_of_nonneg_of_nonpos hρ0.le (hst .good).1
    have := mul_lt_mul_of_pos_left hlt h1ρ
    linarith

private lemma inactive_rv_nonpos_p2 (P : Params) (hStand : P.Standing) {Qbar : ℝ} (hQ0 : 0 ≤ Qbar)
    (σ : Profile) (hpost : IsPostInventorySPE P Qbar σ)
    {q w : ℝ} (hq : 0 ≤ q) (hw : 0 ≤ w) (hI0 : 0 ≤ σ.inv q w)
    (hsv_nn : 0 ≤ σ.supplierValue P q w (σ.inv q w))
    (hinact : ¬ (P.cost q ≤ w ∧ 0 < q ∧ w < q * P.θH)) :
    σ.retailerValue P q w ≤ 0 := by
  rcases hStand with ⟨hθL, hθLH, hk, hρ0, hρ1, hαb0, hαb_lt, hαg_gt, hαg1⟩
  have hθH : 0 < P.θH := lt_trans hθL hθLH
  have hαg0 : 0 < P.αg := pos_of_mul_pos_left (lt_trans hθL hαg_gt) hθH.le
  have hαb1 : P.αb < 1 :=
    lt_trans (lt_of_mul_lt_mul_right (lt_trans hαb_lt hαg_gt) hθH.le) hαg1
  have h1ρ : 0 < 1 - P.ρ := sub_pos.mpr hρ1
  let I := σ.inv q w
  rcases lt_or_ge w (P.cost q) with hw_lt | hcw
  · have hre0 : ∀ Q : ℝ, ∀ s : State, I < Q → σ.react q w I s Q = 0 := by
      intro Q s hIQ
      obtain ⟨hr0, _, hropt⟩ := hpost.2.1 q w I s Q hq hw hI0 hIQ
      have h0 := hropt 0 (le_refl 0) hQ0
      unfold Params.supplierState received at h0
      simp only [if_neg (not_le_of_gt hIQ), add_zero, min_eq_left hIQ.le] at h0
      by_contra hne
      have hr_pos : 0 < σ.react q w I s Q := lt_of_le_of_ne hr0 (Ne.symm hne)
      have hmin_gt : I < min (I + σ.react q w I s Q) Q := lt_min (by linarith) hIQ
      have hmin_le : min (I + σ.react q w I s Q) Q ≤ I + σ.react q w I s Q := min_le_left _ _
      have hc0 : 0 ≤ P.cost q := mul_nonneg hk.le (sq_nonneg q)
      have h1 : (w - P.cost q) * (min (I + σ.react q w I s Q) Q - I) < 0 :=
        mul_neg_of_neg_of_pos (by linarith) (by linarith)
      have h2 : 0 ≤ P.cost q * (I + σ.react q w I s Q - min (I + σ.react q w I s Q) Q) :=
        mul_nonneg hc0 (by linarith)
      linarith
    have hsv_le : ∀ s : State, σ.supplierStateValue P q w I s ≤ (w - P.cost q) * I := by
      intro s
      unfold Profile.supplierStateValue Params.supplierState Profile.recv Profile.made
        received inSeason
      rcases le_or_gt (σ.order q w I s) I with hQI | hIQ
      · rw [if_pos hQI, if_pos hQI, add_zero]
        have := mul_le_mul_of_nonneg_left hQI hw; linarith
      · rw [if_neg (not_le_of_gt hIQ), if_neg (not_le_of_gt hIQ), hre0 _ s hIQ,
          add_zero, min_eq_left hIQ.le]
        linarith
    have hI_eq0 : I = 0 := by
      by_contra hne
      have hI_pos : 0 < I := lt_of_le_of_ne hI0 (Ne.symm hne)
      have hneg : (w - P.cost q) * I < 0 := mul_neg_of_neg_of_pos (by linarith) hI_pos
      unfold Profile.supplierValue Params.prob at hsv_nn
      have := mul_le_mul_of_nonneg_left (hsv_le .good) hρ0.le
      have := mul_le_mul_of_nonneg_left (hsv_le .bad) h1ρ.le
      linarith
    have hov0 : ∀ s : State, σ.orderValue P q w I s (σ.order q w I s) = 0 := by
      intro s
      have hrec0 : σ.recv q w I s (σ.order q w I s) = 0 := by
        obtain ⟨hQs0, _⟩ := hpost.2.2 q w I s hq hw hI0
        unfold Profile.recv received
        rcases le_or_gt (σ.order q w I s) I with hle | hgt
        · rw [if_pos hle]; linarith
        · rw [if_neg (not_le_of_gt hgt), hre0 _ s hgt, add_zero, min_eq_left hgt.le, hI_eq0]
      unfold Profile.orderValue Params.retailerState
      rw [hrec0, mul_zero]
      have hd0 : 0 ≤ P.demand q (P.alpha s) (σ.priceAfter q w I s (σ.order q w I s)) := by
        unfold Params.demand
        rcases s with _ | _ <;> (simp only [Params.alpha]; split_ifs <;> linarith)
      rw [min_eq_right hd0, mul_zero, sub_zero]
    unfold Profile.retailerValue Params.prob
    change P.ρ * σ.orderValue P q w I .good _ + (1 - P.ρ) * σ.orderValue P q w I .bad _ ≤ 0
    rw [hov0 .good, hov0 .bad]; linarith
  · have hw_ge_H : q * P.θH ≤ w := by
      rcases eq_or_lt_of_le hq with rfl | hq_pos
      · simp [hw]
      · by_contra hc; exact hinact ⟨hcw, hq_pos, lt_of_not_ge hc⟩
    have hov_le0 : ∀ s : State, σ.orderValue P q w I s (σ.order q w I s) ≤ 0 := by
      intro s
      obtain ⟨hQs0, _⟩ := hpost.2.2 q w I s hq hw hI0
      have hRs0 : 0 ≤ σ.recv q w I s (σ.order q w I s) := by
        unfold Profile.recv received
        rcases le_or_gt (σ.order q w I s) I with h1 | h1
        · rw [if_pos h1]; exact hQs0
        · rw [if_neg (not_le_of_gt h1)]
          obtain ⟨hr0, _, _⟩ := hpost.2.1 q w I s _ hq hw hI0 h1
          exact le_min (add_nonneg hI0 hr0) hQs0
      let Rs := σ.recv q w I s (σ.order q w I s)
      let ps := σ.priceAfter q w I s (σ.order q w I s)
      unfold Profile.orderValue Params.retailerState
      change ps * min (P.demand q (P.alpha s) ps) Rs - w * Rs ≤ 0
      rcases le_or_gt ps (q * P.θH) with hpH | hpH
      · have hd0 : 0 ≤ P.demand q (P.alpha s) ps := by
          unfold Params.demand
          rcases s with _ | _ <;> (simp only [Params.alpha]; split_ifs <;> linarith)
        have hm0 : 0 ≤ min (P.demand q (P.alpha s) ps) Rs := le_min hd0 hRs0
        have h1 : ps * min (P.demand q (P.alpha s) ps) Rs ≤
            w * min (P.demand q (P.alpha s) ps) Rs :=
          mul_le_mul_of_nonneg_right (le_trans hpH hw_ge_H) hm0
        have h2 : w * min (P.demand q (P.alpha s) ps) Rs ≤ w * Rs :=
          mul_le_mul_of_nonneg_left (min_le_right _ _) hw
        linarith
      · have hpL : q * P.θL < ps :=
          lt_of_le_of_lt (mul_le_mul_of_nonneg_left hθLH.le hq) hpH
        unfold Params.demand
        rw [if_neg (not_le_of_gt hpL), if_neg (not_le_of_gt hpH), add_zero,
          min_eq_left hRs0, mul_zero]
        have := mul_nonneg hw hRs0; linarith
    unfold Profile.retailerValue Params.prob
    change P.ρ * σ.orderValue P q w I .good _ + (1 - P.ρ) * σ.orderValue P q w I .bad _ ≤ 0
    have := mul_le_mul_of_nonneg_left (hov_le0 .good) hρ0.le
    have := mul_le_mul_of_nonneg_left (hov_le0 .bad) h1ρ.le
    linarith

private lemma active_strict_w_p2 (P : Params) (hStand : P.Standing) {Qbar : ℝ} (hQ0 : 0 ≤ Qbar)
    (σ : Profile) (hpost : IsPostInventorySPE P Qbar σ)
    {q w J : ℝ} (hq_pos : 0 < q) (hc_lt_w : P.cost q < w) (hwH : w < q * P.θH) (hJ0 : 0 ≤ J) :
    (∀ s : State, ∀ Q : ℝ,
      σ.recv q w J s Q = min Q (J + Qbar) ∧
      J + σ.made q w J s Q = max J (min Q (J + Qbar))) ∧
    (∀ s : State,
      0 ≤ σ.order q w J s ∧
      0 ≤ σ.priceAfter q w J s (σ.order q w J s) ∧
      ∀ Q' p' : ℝ, 0 ≤ Q' → 0 ≤ p' →
        P.stepOnePayoff q w (P.alpha s) (J + Qbar) Q' p' ≤
          P.stepOnePayoff q w (P.alpha s) (J + Qbar) (σ.order q w J s)
            (σ.priceAfter q w J s (σ.order q w J s))) ∧
    σ.recv q w J .good (σ.order q w J .good) = min P.αg (J + Qbar) ∧
    min P.αb (J + Qbar) ≤ σ.recv q w J .bad (σ.order q w J .bad) ∧
    σ.recv q w J .bad (σ.order q w J .bad) ≤ min (J + Qbar) 1 ∧
    ((q * P.θL - w) * min (J + Qbar) 1 < (q * P.θH - w) * min P.αb (J + Qbar) →
      σ.recv q w J .bad (σ.order q w J .bad) = min P.αb (J + Qbar)) ∧
    ((q * P.θH - w) * min P.αb (J + Qbar) < (q * P.θL - w) * min (J + Qbar) 1 →
      σ.recv q w J .bad (σ.order q w J .bad) = min (J + Qbar) 1) := by
  rcases hStand with ⟨hθL, hθLH, hk, hρ0, hρ1, hαb0, hαb_lt, hαg_gt, hαg1⟩
  have hStand' : P.Standing := ⟨hθL, hθLH, hk, hρ0, hρ1, hαb0, hαb_lt, hαg_gt, hαg1⟩
  have hθH : 0 < P.θH := lt_trans hθL hθLH
  have hαg0 : 0 < P.αg := pos_of_mul_pos_left (lt_trans hθL hαg_gt) hθH.le
  have hαb_αg : P.αb < P.αg := lt_of_mul_lt_mul_right (lt_trans hαb_lt hαg_gt) hθH.le
  have hαb1 : P.αb < 1 := lt_trans hαb_αg hαg1
  have hc_pos : 0 < P.cost q := mul_pos hk (pow_pos hq_pos 2)
  have hw_pos : 0 < w := lt_trans hc_pos hc_lt_w
  have hqLH : q * P.θL < q * P.θH := mul_lt_mul_of_pos_left hθLH hq_pos
  have hwH0 : 0 < q * P.θH - w := sub_pos.mpr hwH
  have hreact_eq : ∀ s : State, ∀ Q : ℝ, J < Q → σ.react q w J s Q = min Qbar (Q - J) := by
    intro s Q hJQ
    obtain ⟨_, _, hropt⟩ := hpost.2.1 q w J s Q hq_pos.le hw_pos.le hJ0 hJQ
    let Is := min Qbar (Q - J)
    have hge := hropt Is (le_min hQ0 (sub_pos.mpr hJQ).le) (min_le_left _ _)
    have hJIs : J + Is ≤ Q := by have := min_le_right Qbar (Q - J); dsimp [Is]; linarith
    unfold Params.supplierState received at hge
    simp only [if_neg (not_le_of_gt hJQ), min_eq_left hJIs] at hge
    rcases lt_trichotomy (σ.react q w J s Q) Is with hlt | heq | hgt
    · exfalso
      rw [min_eq_left (by linarith)] at hge
      have := mul_lt_mul_of_pos_left (by linarith : J + σ.react q w J s Q < J + Is)
        (sub_pos.mpr hc_lt_w)
      linarith
    · exact heq
    · exfalso
      have hIs_eq : Is = Q - J := by
        dsimp [Is] at hgt ⊢
        rcases le_or_gt Qbar (Q - J) with h1 | h1
        · rw [min_eq_left h1] at hgt; linarith
        · exact min_eq_right h1.le
      have hgtQ : Q < J + σ.react q w J s Q := by linarith
      rw [min_eq_right hgtQ.le, hIs_eq, show J + (Q - J) = Q by ring] at hge
      have := mul_lt_mul_of_pos_left hgtQ hc_pos
      linarith
  have hrm : ∀ s : State, ∀ Q : ℝ,
      σ.recv q w J s Q = min Q (J + Qbar) ∧
      J + σ.made q w J s Q = max J (min Q (J + Qbar)) := by
    intro s Q
    unfold Profile.recv Profile.made received inSeason
    rcases le_or_gt Q J with hQJ | hJQ
    · rw [if_pos hQJ, if_pos hQJ, min_eq_left (by linarith), max_eq_left hQJ, add_zero]
      exact ⟨rfl, rfl⟩
    · rw [if_neg (not_le_of_gt hJQ), if_neg (not_le_of_gt hJQ), hreact_eq s Q hJQ]
      have hsum : J + min Qbar (Q - J) = min Q (J + Qbar) := by
        rcases le_or_gt Qbar (Q - J) with h1 | h1
        · rw [min_eq_left h1, min_eq_right (by linarith)]
        · rw [min_eq_right h1.le, min_eq_left (by linarith)]; ring
      rw [hsum, min_eq_left (min_le_left Q (J + Qbar)),
        max_eq_right (le_min hJQ.le (by linarith))]
      exact ⟨rfl, rfl⟩
  have hstep_opt : ∀ s : State,
      0 ≤ σ.order q w J s ∧
      0 ≤ σ.priceAfter q w J s (σ.order q w J s) ∧
      ∀ Q' p' : ℝ, 0 ≤ Q' → 0 ≤ p' →
        P.stepOnePayoff q w (P.alpha s) (J + Qbar) Q' p' ≤
          P.stepOnePayoff q w (P.alpha s) (J + Qbar) (σ.order q w J s)
            (σ.priceAfter q w J s (σ.order q w J s)) := by
    intro s
    have hmb : ∀ Q : ℝ, 0 ≤ σ.made q w J s Q ∧ σ.made q w J s Q ≤ Qbar := by
      intro Q; unfold Profile.made inSeason
      rcases le_or_gt Q J with h1 | h1
      · rw [if_pos h1]; exact ⟨le_refl 0, hQ0⟩
      · rw [if_neg (not_le_of_gt h1)]
        obtain ⟨hr0, hrQ, _⟩ := hpost.2.1 q w J s Q hq_pos.le hw_pos.le hJ0 h1
        exact ⟨hr0, hrQ⟩
    obtain ⟨hQo0, hQo_opt⟩ := hpost.2.2 q w J s hq_pos.le hw_pos.le hJ0
    obtain ⟨hm0, hmQ⟩ := hmb (σ.order q w J s)
    obtain ⟨hp0, _⟩ := hpost.1 q w J s (σ.order q w J s) _ hq_pos.le hw_pos.le hJ0 hQo0 hm0 hmQ
    refine ⟨hQo0, hp0, fun Q' p' hQ' hp' => ?_⟩
    obtain ⟨hm'0, hm'Q⟩ := hmb Q'
    obtain ⟨_, hp'_opt⟩ := hpost.1 q w J s Q' _ hq_pos.le hw_pos.le hJ0 hQ' hm'0 hm'Q
    have hrec_made : received J Q' (σ.made q w J s Q') = σ.recv q w J s Q' := by
      unfold Profile.made Profile.recv received inSeason
      rcases le_or_gt Q' J with h1 | h1
      · rw [if_pos h1, if_pos h1]
      · rw [if_neg (not_le_of_gt h1), if_neg (not_le_of_gt h1), if_neg (not_le_of_gt h1)]
    have h1 : P.stepOnePayoff q w (P.alpha s) (J + Qbar) Q' p' ≤ σ.orderValue P q w J s Q' := by
      unfold Params.stepOnePayoff Profile.orderValue Params.retailerState Profile.priceAfter
      rw [← (hrm s Q').1, ← hrec_made]
      exact hp'_opt p' hp'
    have h2 := hQo_opt Q' hQ'
    have h3 : σ.orderValue P q w J s (σ.order q w J s) =
        P.stepOnePayoff q w (P.alpha s) (J + Qbar) (σ.order q w J s)
          (σ.priceAfter q w J s (σ.order q w J s)) := by
      unfold Profile.orderValue Params.retailerState Params.stepOnePayoff
      rw [(hrm s _).1]
    linarith
  have hmin_eq_of_pay : ∀ θ α S R : ℝ, 0 ≤ α → 0 ≤ R → R ≤ S → w < θ →
      (θ - w) * min α S ≤ θ * min α R - w * R → R = min α S := by
    intro θ α S R _ _ hRS hwθ hge
    rcases lt_trichotomy R (min α S) with hlt | heq | hgt
    · exfalso
      rw [min_eq_right (le_trans hlt.le (min_le_left α S))] at hge
      have := mul_lt_mul_of_pos_left hlt (sub_pos.mpr hwθ)
      linarith
    · exact heq
    · exfalso
      have hαS : α ≤ S := by
        by_contra hc; rw [min_eq_right (lt_of_not_ge hc).le] at hgt; linarith
      rw [min_eq_left hαS] at hgt hge
      rw [min_eq_left hgt.le] at hge
      have := mul_lt_mul_of_pos_left hgt hw_pos
      linarith
  let S := J + Qbar
  have hS0 : 0 ≤ S := add_nonneg hJ0 hQ0
  have hrule := retailer_stage_rule P hStand' q w S hq_pos hw_pos.le hwH hS0
  have hRg : σ.recv q w J .good (σ.order q w J .good) = min P.αg S := by
    rw [(hrm .good _).1]
    obtain ⟨hQo0, hp0, hopt⟩ := hstep_opt .good
    rcases eq_or_lt_of_le hS0 with hS_z | hS_pos
    · have h1 : min (σ.order q w J .good) S = 0 :=
        le_antisymm (by rw [← hS_z]; exact min_le_right _ _) (le_min hQo0 hS0)
      have h2 : min P.αg S = 0 :=
        le_antisymm (by rw [← hS_z]; exact min_le_right _ _) (le_min hαg0.le hS0)
      exact h1.trans h2.symm
    · have hp_eq : σ.priceAfter q w J .good (σ.order q w J .good) = q * P.θH :=
        hrule.2.1 hS_pos _ _ hQo0 hp0 hopt
      have hge := hopt (min P.αg S) (q * P.θH) (le_min hαg0.le hS0) (mul_pos hq_pos hθH).le
      rw [hp_eq] at hge
      unfold Params.stepOnePayoff Params.demand Params.alpha at hge
      rw [if_neg (not_le_of_gt hqLH), if_pos (le_refl _), zero_add,
        min_eq_left (min_le_right P.αg S), min_eq_right (min_le_left P.αg S)] at hge
      exact hmin_eq_of_pay (q * P.θH) P.αg S (min (σ.order q w J .good) S) hαg0.le
        (le_min hQo0 hS0) (min_le_right _ _) hwH (by linarith)
  obtain ⟨hQob0, hpb0, hopt_b⟩ := hstep_opt .bad
  let Rb := min (σ.order q w J .bad) S
  let pb := σ.priceAfter q w J .bad (σ.order q w J .bad)
  have hRb_eq : σ.recv q w J .bad (σ.order q w J .bad) = Rb := (hrm .bad _).1
  have hRb0 : 0 ≤ Rb := le_min hQob0 hS0
  have hRbS : Rb ≤ S := min_le_right _ _
  have hge_ab : (q * P.θH - w) * min P.αb S ≤ P.stepOnePayoff q w P.αb S (σ.order q w J .bad) pb := by
    have h1 := hopt_b (min P.αb S) (q * P.θH) (le_min hαb0.le hS0) (mul_pos hq_pos hθH).le
    refine le_trans ?_ h1
    unfold Params.stepOnePayoff Params.demand Params.alpha
    rw [if_neg (not_le_of_gt hqLH), if_pos (le_refl _), zero_add,
      min_eq_left (min_le_right P.αb S), min_eq_right (min_le_left P.αb S)]
    linarith
  have hRb_lo : min P.αb S ≤ Rb := by
    by_contra hc
    have hlt : Rb < min P.αb S := lt_of_not_ge hc
    have hRb_lt1 : Rb < 1 := lt_of_lt_of_le hlt (le_trans (min_le_left _ _) hαb1.le)
    have hpay_lt : P.stepOnePayoff q w P.αb S (σ.order q w J .bad) pb <
        (q * P.θH - w) * min P.αb S := by
      unfold Params.stepOnePayoff Params.demand
      change pb * min (_ + _) Rb - w * Rb < _
      rcases le_or_gt pb (q * P.θH) with hpH | hpH
      · have hd1 : (if pb ≤ q * P.θL then 1 - P.αb else 0) + (if pb ≤ q * P.θH then P.αb else 0) ≤ 1 := by
          split_ifs <;> linarith
        have hm_le : min ((if pb ≤ q * P.θL then 1 - P.αb else 0) +
            if pb ≤ q * P.θH then P.αb else 0) Rb ≤ Rb := min_le_right _ _
        have hm0 : 0 ≤ min ((if pb ≤ q * P.θL then 1 - P.αb else 0) +
            if pb ≤ q * P.θH then P.αb else 0) Rb := by
          refine le_min ?_ hRb0; split_ifs <;> linarith
        have h1 : pb * min ((if pb ≤ q * P.θL then 1 - P.αb else 0) +
            if pb ≤ q * P.θH then P.αb else 0) Rb ≤ q * P.θH * Rb :=
          le_trans (mul_le_mul_of_nonneg_right hpH hm0)
            (mul_le_mul_of_nonneg_left hm_le (mul_pos hq_pos hθH).le)
        have h2 : (q * P.θH - w) * Rb < (q * P.θH - w) * min P.αb S :=
          mul_lt_mul_of_pos_left hlt hwH0
        linarith
      · have hpL : q * P.θL < pb := lt_trans hqLH hpH
        rw [if_neg (not_le_of_gt hpL), if_neg (not_le_of_gt hpH), add_zero,
          min_eq_left hRb0, mul_zero]
        have : 0 ≤ w * Rb := mul_nonneg hw_pos.le hRb0
        have : 0 < (q * P.θH - w) * min P.αb S := mul_pos hwH0 (lt_of_le_of_lt hRb0 hlt)
        linarith
    linarith
  have hRb_hi : Rb ≤ min S 1 := by
    refine le_min hRbS ?_
    by_contra hc
    have hgt1 : 1 < Rb := lt_of_not_ge hc
    have hS_ge1 : 1 ≤ S := le_trans hgt1.le hRbS
    have h1 := hopt_b 1 pb zero_le_one hpb0
    unfold Params.stepOnePayoff at h1
    change pb * min (P.demand q P.αb pb) (min 1 S) - w * min 1 S ≤
      pb * min (P.demand q P.αb pb) Rb - w * Rb at h1
    rw [min_eq_left hS_ge1] at h1
    have hd_le1 : P.demand q P.αb pb ≤ 1 := by unfold Params.demand; split_ifs <;> linarith
    rw [min_eq_left hd_le1, min_eq_left (le_trans hd_le1 hgt1.le)] at h1
    have := mul_lt_mul_of_pos_left hgt1 hw_pos
    linarith
  refine ⟨hrm, hstep_opt, hRg, ?_, ?_, ?_, ?_⟩
  · rwa [hRb_eq]
  · rwa [hRb_eq]
  · intro hH
    rw [hRb_eq]
    have hp_eq : pb = q * P.θH := hrule.2.2.2 hH _ _ hQob0 hpb0 hopt_b
    have hge := hge_ab
    rw [hp_eq] at hge
    unfold Params.stepOnePayoff Params.demand at hge
    rw [if_neg (not_le_of_gt hqLH), if_pos (le_refl _), zero_add] at hge
    exact hmin_eq_of_pay (q * P.θH) P.αb S Rb hαb0.le hRb0 hRbS hwH (by dsimp [Rb]; linarith)
  · intro hL
    rw [hRb_eq]
    have hwL : w < q * P.θL := by
      have hpos : 0 ≤ (q * P.θH - w) * min P.αb S := mul_nonneg hwH0.le (le_min hαb0.le hS0)
      have hLpos : 0 < (q * P.θL - w) * min S 1 := lt_of_le_of_lt hpos hL
      by_contra hc
      have := mul_nonpos_of_nonpos_of_nonneg (by linarith : q * P.θL - w ≤ 0)
        (le_min hS0 zero_le_one)
      linarith
    have hp_eq : pb = q * P.θL := hrule.2.2.1 hL _ _ hQob0 hpb0 hopt_b
    have hge := hopt_b (min S 1) (q * P.θL) (le_min hS0 zero_le_one) (mul_pos hq_pos hθL).le
    dsimp [pb] at hp_eq
    rw [hp_eq] at hge
    unfold Params.stepOnePayoff Params.demand Params.alpha at hge
    rw [if_pos (le_refl _), if_pos hqLH.le, sub_add_cancel,
      min_eq_left (min_le_left S 1), min_eq_right (min_le_right S 1)] at hge
    have hR1 := hmin_eq_of_pay (q * P.θL) 1 S Rb zero_le_one hRb0 hRbS hwL
      (by rw [min_comm 1 S]; dsimp [Rb]; linarith)
    rwa [min_comm 1 S] at hR1


private noncomputable def fh_p2 (P : Params) (Qbar q w J : ℝ) : ℝ :=
  P.ρ * (w * min P.αg (J + Qbar) - P.cost q * max J (min P.αg (J + Qbar))) +
    (1 - P.ρ) * (w * min P.αb (J + Qbar) - P.cost q * max J (min P.αb (J + Qbar)))

private noncomputable def fl_p2 (P : Params) (Qbar q w J : ℝ) : ℝ :=
  P.ρ * (w * min P.αg (J + Qbar) - P.cost q * max J (min P.αg (J + Qbar))) +
    (1 - P.ρ) * (w * min (J + Qbar) 1 - P.cost q * max J (min (J + Qbar) 1))

private lemma sv_mono_aux_p2 {w c J R₁ R₂ : ℝ} (hc : 0 ≤ c) (hcw : c ≤ w) (hle : R₁ ≤ R₂) :
    w * R₁ - c * max J R₁ ≤ w * R₂ - c * max J R₂ := by
  rcases le_or_gt R₂ J with h2 | h2
  · rw [max_eq_left (le_trans hle h2), max_eq_left h2]
    have := mul_le_mul_of_nonneg_left hle (le_trans hc hcw)
    linarith
  · rcases le_or_gt J R₁ with h1 | h1
    · rw [max_eq_right h1, max_eq_right h2.le]
      have := mul_le_mul_of_nonneg_left hle (sub_nonneg.mpr hcw)
      linarith
    · rw [max_eq_left h1.le, max_eq_right h2.le]
      have hA : w * R₁ - c * J ≤ (w - c) * J := by
        have := mul_le_mul_of_nonneg_left h1.le (le_trans hc hcw); linarith
      have hB : (w - c) * J ≤ (w - c) * R₂ :=
        mul_le_mul_of_nonneg_left h2.le (sub_nonneg.mpr hcw)
      linarith

private lemma sv_bounds_strict_w_p2 (P : Params) (hStand : P.Standing) {Qbar : ℝ} (hQ0 : 0 ≤ Qbar)
    (σ : Profile) (hpost : IsPostInventorySPE P Qbar σ)
    {q w J : ℝ} (hq_pos : 0 < q) (hc_lt_w : P.cost q < w) (hwH : w < q * P.θH) (hJ0 : 0 ≤ J) :
    fh_p2 P Qbar q w J ≤ σ.supplierValue P q w J ∧
    σ.supplierValue P q w J ≤ fl_p2 P Qbar q w J ∧
    ((q * P.θL - w) * min (J + Qbar) 1 < (q * P.θH - w) * min P.αb (J + Qbar) →
      σ.supplierValue P q w J = fh_p2 P Qbar q w J) ∧
    ((q * P.θH - w) * min P.αb (J + Qbar) < (q * P.θL - w) * min (J + Qbar) 1 →
      σ.supplierValue P q w J = fl_p2 P Qbar q w J) := by
  obtain ⟨hrm, _, hRg, hRb_lo, hRb_hi, hH, hL⟩ :=
    active_strict_w_p2 P hStand hQ0 σ hpost hq_pos hc_lt_w hwH hJ0
  rcases hStand with ⟨_, _, hk, hρ0, hρ1, _, _, _, _⟩
  have h1ρ : 0 < 1 - P.ρ := sub_pos.mpr hρ1
  have hc0 : 0 ≤ P.cost q := mul_nonneg hk.le (sq_nonneg q)
  have hsv_eq : σ.supplierValue P q w J =
      P.ρ * (w * min P.αg (J + Qbar) - P.cost q * max J (min P.αg (J + Qbar))) +
        (1 - P.ρ) * (w * σ.recv q w J .bad (σ.order q w J .bad) -
          P.cost q * max J (σ.recv q w J .bad (σ.order q w J .bad))) := by
    unfold Profile.supplierValue Profile.supplierStateValue
    dsimp only [Params.prob, Params.supplierState]
    rw [(hrm .good (σ.order q w J .good)).2, ← (hrm .good (σ.order q w J .good)).1, hRg,
      (hrm .bad (σ.order q w J .bad)).2, ← (hrm .bad (σ.order q w J .bad)).1]
  rw [hsv_eq]
  unfold fh_p2 fl_p2
  refine ⟨?_, ?_, fun hh => by rw [hH hh], fun hl => by rw [hL hl]⟩
  · have := mul_le_mul_of_nonneg_left (sv_mono_aux_p2 (J := J) hc0 hc_lt_w.le hRb_lo) h1ρ.le
    linarith
  · have := mul_le_mul_of_nonneg_left (sv_mono_aux_p2 (J := J) hc0 hc_lt_w.le hRb_hi) h1ρ.le
    linarith

private lemma fh_max_p2 (P : Params) (hStand : P.Standing) {Qbar q w J : ℝ}
    (hQ0 : 0 ≤ Qbar) (_hq_pos : 0 < q) (hc_lt_w : P.cost q < w) (_hJ0 : 0 ≤ J) :
    fh_p2 P Qbar q w J ≤
      max (fh_p2 P Qbar q w P.αb) (fh_p2 P Qbar q w (max P.αb (P.αg - Qbar))) := by
  rcases hStand with ⟨hθL, hθLH, hk, hρ0, hρ1, hαb0, hαb_lt, hαg_gt, _⟩
  have hθH : 0 < P.θH := lt_trans hθL hθLH
  have hαb_αg : P.αb < P.αg := lt_of_mul_lt_mul_right (lt_trans hαb_lt hαg_gt) hθH.le
  have h1ρ : 0 < 1 - P.ρ := sub_pos.mpr hρ1
  have hc0 : 0 ≤ P.cost q := mul_nonneg hk.le (sq_nonneg q)
  have hwc : 0 < w - P.cost q := sub_pos.mpr hc_lt_w
  let B := max P.αb (P.αg - Qbar)
  have hB_ab : P.αb ≤ B := le_max_left _ _
  have hB_ag : B ≤ P.αg := max_le hαb_αg.le (by linarith)
  rcases le_or_gt J P.αb with hJab | hJab
  · refine le_trans ?_ (le_max_left _ _)
    unfold fh_p2
    have hgJ : max J (min P.αg (J + Qbar)) = min P.αg (J + Qbar) :=
      max_eq_right (le_min (le_trans hJab hαb_αg.le) (by linarith))
    have hbJ : max J (min P.αb (J + Qbar)) = min P.αb (J + Qbar) :=
      max_eq_right (le_min hJab (by linarith))
    have hgab : max P.αb (min P.αg (P.αb + Qbar)) = min P.αg (P.αb + Qbar) :=
      max_eq_right (le_min hαb_αg.le (by linarith))
    have hbab : min P.αb (P.αb + Qbar) = P.αb := min_eq_left (by linarith)
    rw [hgJ, hbJ, hgab, hbab, max_self]
    have h1 : min P.αg (J + Qbar) ≤ min P.αg (P.αb + Qbar) := min_le_min_left P.αg (by linarith)
    have h2 : min P.αb (J + Qbar) ≤ P.αb := min_le_left _ _
    have := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h1 hwc.le) hρ0.le
    have := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h2 hwc.le) h1ρ.le
    linarith
  · rcases le_or_gt B J with hBJ | hJB
    · refine le_trans ?_ (le_max_right _ _)
      unfold fh_p2
      have hBQ : P.αg ≤ B + Qbar := by have := le_max_right P.αb (P.αg - Qbar); dsimp [B]; linarith
      have hJQ : P.αg ≤ J + Qbar := by linarith
      rw [min_eq_left hJQ, min_eq_left (by linarith : P.αb ≤ J + Qbar),
        max_eq_left hJab.le, min_eq_left hBQ, min_eq_left (by linarith : P.αb ≤ B + Qbar),
        max_eq_right hB_ag, max_eq_left hB_ab]
      have h1 : P.cost q * P.αg ≤ P.cost q * max J P.αg :=
        mul_le_mul_of_nonneg_left (le_max_right J P.αg) hc0
      have h2 : P.cost q * B ≤ P.cost q * J := mul_le_mul_of_nonneg_left hBJ hc0
      have := mul_le_mul_of_nonneg_left (by linarith :
        w * P.αg - P.cost q * max J P.αg ≤ w * P.αg - P.cost q * P.αg) hρ0.le
      have := mul_le_mul_of_nonneg_left (by linarith :
        w * P.αb - P.cost q * J ≤ w * P.αb - P.cost q * B) h1ρ.le
      linarith
    · have hB_eq : B = P.αg - Qbar := max_eq_right (by
        by_contra hc
        have hlt : P.αg - Qbar < P.αb := lt_of_not_ge hc
        have : B = P.αb := max_eq_left hlt.le
        linarith)
      have hlin : ∀ t : ℝ, P.αb ≤ t → t ≤ B →
          fh_p2 P Qbar q w t = (P.ρ * w - P.cost q) * t +
            (P.ρ * (w - P.cost q) * Qbar + (1 - P.ρ) * w * P.αb) := by
        intro t ht_lo ht_hi
        have htQ : t + Qbar ≤ P.αg := by linarith
        unfold fh_p2
        rw [min_eq_right htQ, max_eq_right (by linarith : t ≤ t + Qbar),
          min_eq_left (by linarith : P.αb ≤ t + Qbar), max_eq_left ht_lo]
        ring
      rw [hlin J hJab.le hJB.le, hlin P.αb (le_refl _) hB_ab, hlin B hB_ab (le_refl _)]
      rcases le_or_gt (P.ρ * w - P.cost q) 0 with hsl | hsl
      · refine le_trans ?_ (le_max_left _ _)
        have := mul_le_mul_of_nonpos_left hJab.le hsl; linarith
      · refine le_trans ?_ (le_max_right _ _)
        have := mul_le_mul_of_nonneg_left hJB.le hsl.le; linarith

private lemma rv_lb_strict_w_p2 (P : Params) (hStand : P.Standing) {Qbar : ℝ} (hQ0 : 0 ≤ Qbar)
    (σ : Profile) (hpost : IsPostInventorySPE P Qbar σ)
    {q w : ℝ} (hq_pos : 0 < q) (hc_lt_w : P.cost q < w) (hwH : w < q * P.θH)
    (hI0 : 0 ≤ σ.inv q w) :
    P.ρ * ((q * P.θH - w) * min P.αg (σ.inv q w + Qbar)) +
      (1 - P.ρ) * max ((q * P.θH - w) * min P.αb (σ.inv q w + Qbar))
        ((q * P.θL - w) * min (σ.inv q w + Qbar) 1) ≤
      σ.retailerValue P q w := by
  obtain ⟨hrm, hstep_opt, _, _, _, _, _⟩ :=
    active_strict_w_p2 P hStand hQ0 σ hpost hq_pos hc_lt_w hwH hI0
  rcases hStand with ⟨hθL, hθLH, _, hρ0, hρ1, hαb0, _, hαg_gt, _⟩
  have hθH : 0 < P.θH := lt_trans hθL hθLH
  have hαg0 : 0 < P.αg := pos_of_mul_pos_left (lt_trans hθL hαg_gt) hθH.le
  have h1ρ : 0 < 1 - P.ρ := sub_pos.mpr hρ1
  have hqLH : q * P.θL < q * P.θH := mul_lt_mul_of_pos_left hθLH hq_pos
  let J := σ.inv q w
  let S := J + Qbar
  have hS0 : 0 ≤ S := add_nonneg hI0 hQ0
  have hov_eq : ∀ s : State, σ.orderValue P q w J s (σ.order q w J s) =
      P.stepOnePayoff q w (P.alpha s) S (σ.order q w J s)
        (σ.priceAfter q w J s (σ.order q w J s)) := by
    intro s
    unfold Profile.orderValue Params.retailerState Params.stepOnePayoff
    rw [(hrm s _).1]
  have hg_ge : (q * P.θH - w) * min P.αg S ≤ σ.orderValue P q w J .good (σ.order q w J .good) := by
    rw [hov_eq .good]
    have h1 := (hstep_opt .good).2.2 (min P.αg S) (q * P.θH) (le_min hαg0.le hS0)
      (mul_pos hq_pos hθH).le
    refine le_trans ?_ h1
    unfold Params.stepOnePayoff Params.demand Params.alpha
    rw [if_neg (not_le_of_gt hqLH), if_pos (le_refl _), zero_add,
      min_eq_left (min_le_right P.αg S), min_eq_right (min_le_left P.αg S)]
    linarith
  have hbH_ge : (q * P.θH - w) * min P.αb S ≤ σ.orderValue P q w J .bad (σ.order q w J .bad) := by
    rw [hov_eq .bad]
    have h1 := (hstep_opt .bad).2.2 (min P.αb S) (q * P.θH) (le_min hαb0.le hS0)
      (mul_pos hq_pos hθH).le
    refine le_trans ?_ h1
    unfold Params.stepOnePayoff Params.demand Params.alpha
    rw [if_neg (not_le_of_gt hqLH), if_pos (le_refl _), zero_add,
      min_eq_left (min_le_right P.αb S), min_eq_right (min_le_left P.αb S)]
    linarith
  have hbL_ge : (q * P.θL - w) * min S 1 ≤ σ.orderValue P q w J .bad (σ.order q w J .bad) := by
    rw [hov_eq .bad]
    have h1 := (hstep_opt .bad).2.2 (min S 1) (q * P.θL) (le_min hS0 zero_le_one)
      (mul_pos hq_pos hθL).le
    refine le_trans ?_ h1
    unfold Params.stepOnePayoff Params.demand Params.alpha
    rw [if_pos (le_refl _), if_pos hqLH.le, sub_add_cancel,
      min_eq_left (min_le_left S 1), min_eq_right (min_le_right S 1)]
    linarith
  have hb_ge := max_le hbH_ge hbL_ge
  unfold Profile.retailerValue Params.prob
  change _ ≤ P.ρ * σ.orderValue P q w J .good _ + (1 - P.ρ) * σ.orderValue P q w J .bad _
  have := mul_le_mul_of_nonneg_left hg_ge hρ0.le
  have := mul_le_mul_of_nonneg_left hb_ge h1ρ.le
  linarith

private lemma lb_vos_p2 (P : Params) (hStand : P.Standing) (hFocus : P.Focus)
    {Qbar : ℝ} (hQ0 : 0 ≤ Qbar) {σ : Profile} (hSPE : IsSPE P Qbar σ) :
    P.V_OS Qbar ≤ σ.retailerValue P σ.q σ.w := by
  rcases hSPE with ⟨hpost, hinv, _, _, hropt⟩
  obtain ⟨hθH, hαg0, hαb_αg, hαb1, h1ρ, _, _, _, _⟩ := standing_focus_p2 P hStand hFocus
  rcases hStand with ⟨hθL, hθLH, hk, hρ0, hρ1, hαb0, hαb_lt, hαg_gt, hαg1⟩
  have hStand' : P.Standing := ⟨hθL, hθLH, hk, hρ0, hρ1, hαb0, hαb_lt, hαg_gt, hαg1⟩
  let S := P.supplyS Qbar
  have hS_lo : P.αg ≤ S := le_min (by linarith) hαg1.le
  have hS_hi : S ≤ 1 := min_le_right _ _
  obtain ⟨hDS, hYS_pos, _, hYS_lt, hYS_f⟩ := y_props_p2 P hStand' hFocus hS_lo hS_hi
  let qstar := P.Y S / (2 * P.k)
  let wstar := P.Y S ^ 2 / (4 * P.k)
  have hqs_pos : 0 < qstar := div_pos hYS_pos (by linarith)
  have hws_pos : 0 < wstar := div_pos (pow_pos hYS_pos 2) (by linarith)
  have hc_qs : P.cost qstar = wstar := by
    dsimp [qstar, wstar]; unfold Params.cost; field_simp [hk.ne']; ring
  have hws_lt_c1ρ : wstar < P.cost qstar / (1 - P.ρ) := by
    rw [hc_qs, lt_div_iff₀ h1ρ]
    have : wstar * (1 - P.ρ) < wstar * 1 := mul_lt_mul_of_pos_left (by linarith) hws_pos
    linarith
  have hws_lt_L : wstar < qstar * P.θL := by
    dsimp [qstar, wstar]
    rw [div_mul_eq_mul_div, div_lt_div_iff₀ (by linarith : 0 < 4 * P.k) (by linarith : 0 < 2 * P.k)]
    have := mul_lt_mul_of_pos_left hYS_lt (mul_pos hYS_pos hk)
    linarith
  have hlow_qs : (qstar * P.θH - wstar) * P.αb < (qstar * P.θL - wstar) * S := by
    dsimp [qstar, wstar]
    have hid1 : P.Y S / (2 * P.k) * P.θH - P.Y S ^ 2 / (4 * P.k) =
        P.Y S / (4 * P.k) * (2 * P.θH - P.Y S) := by field_simp [hk.ne']; ring
    have hid2 : P.Y S / (2 * P.k) * P.θL - P.Y S ^ 2 / (4 * P.k) =
        P.Y S / (4 * P.k) * (2 * P.θL - P.Y S) := by field_simp [hk.ne']; ring
    rw [hid1, hid2]
    have hfac : 0 < P.Y S / (4 * P.k) := div_pos hYS_pos (by linarith)
    have hlt_inner : (2 * P.θH - P.Y S) * P.αb < (2 * P.θL - P.Y S) * S := by linarith
    have := mul_lt_mul_of_pos_left hlt_inner hfac
    linarith
  by_contra hlt_c
  have hgap : 0 < P.V_OS Qbar - σ.retailerValue P σ.q σ.w := sub_pos.mpr (lt_of_not_ge hlt_c)
  let δ1 := (qstar * P.θL - wstar) * S - (qstar * P.θH - wstar) * P.αb
  let δ2 := qstar * P.θL - wstar
  let δ3 := (P.V_OS Qbar - σ.retailerValue P σ.q σ.w) / (2 * (P.ρ * P.αg + (1 - P.ρ) * S))
  let δ4 := P.cost qstar / (1 - P.ρ) - wstar
  have hδ1 : 0 < δ1 := sub_pos.mpr hlow_qs
  have hδ2 : 0 < δ2 := sub_pos.mpr hws_lt_L
  have hδ3 : 0 < δ3 := div_pos hgap (mul_pos (by norm_num) hDS)
  have hδ4 : 0 < δ4 := sub_pos.mpr hws_lt_c1ρ
  let ε := min (min (δ1 / 2) (δ2 / 2)) (min (δ4 / 2) δ3)
  have hε_pos : 0 < ε := lt_min (lt_min (half_pos hδ1) (half_pos hδ2)) (lt_min (half_pos hδ4) hδ3)
  have hε1 : ε ≤ δ1 / 2 := le_trans (min_le_left _ _) (min_le_left _ _)
  have hε2 : ε ≤ δ2 / 2 := le_trans (min_le_left _ _) (min_le_right _ _)
  have hε4 : ε ≤ δ4 / 2 := le_trans (min_le_right _ _) (min_le_left _ _)
  have hε3 : ε ≤ δ3 := le_trans (min_le_right _ _) (min_le_right _ _)
  let wε := wstar + ε
  have hwε_gt_c : P.cost qstar < wε := by rw [hc_qs]; dsimp [wε]; linarith
  have hwε0 : 0 ≤ wε := (lt_trans hws_pos (by dsimp [wε]; linarith)).le
  have hwε_lt_L : wε < qstar * P.θL := by dsimp [wε, δ2] at *; linarith
  have hwε_lt_H : wε < qstar * P.θH := lt_trans hwε_lt_L (mul_lt_mul_of_pos_left hθLH hqs_pos)
  have hlow_ε : (qstar * P.θH - wε) * P.αb < (qstar * P.θL - wε) * S := by
    have : ε * (S - P.αb) ≤ ε := mul_le_of_le_one_right hε_pos.le (by linarith)
    dsimp [wε, δ1] at *; linarith
  obtain ⟨hIε0, hIε_opt⟩ := hinv qstar wε hqs_pos.le hwε0
  have hS_le : S ≤ σ.inv qstar wε + Qbar := by
    rcases lt_or_ge Qbar (1 - P.αg) with hQmed | hQhi
    · have hS_eq : S = P.αg + Qbar := min_eq_left (by linarith)
      rw [hS_eq] at hlow_ε ⊢
      have hresp := (supplier_response_medium P hStand' Qbar hQ0 hQmed σ hpost qstar wε hqs_pos
        hwε_gt_c hlow_ε).1 (by dsimp [wε, δ4] at *; linarith)
      have hmem : σ.inv qstar wε ∈ ({P.αg} : Set ℝ) := by
        rw [← hresp]; exact ⟨hIε0, hIε_opt⟩
      rw [Set.mem_singleton_iff.mp hmem]
    · have hS_eq : S = 1 := min_eq_right (by linarith)
      rw [hS_eq, mul_one] at hlow_ε
      rw [hS_eq]
      have hresp := supplier_response_high P hStand' Qbar hQhi σ hpost qstar wε hqs_pos hwε_gt_c hlow_ε
      have hmem : σ.inv qstar wε ∈ Set.Icc (max 0 (1 - Qbar)) P.αg := by
        rw [← hresp]; exact ⟨hIε0, hIε_opt⟩
      have := le_trans (le_max_right 0 (1 - Qbar)) hmem.1
      linarith
  have hlb := rv_lb_strict_w_p2 P hStand' hQ0 σ hpost hqs_pos hwε_gt_c hwε_lt_H hIε0
  have hg_eq : min P.αg (σ.inv qstar wε + Qbar) = P.αg := min_eq_left (le_trans hS_lo hS_le)
  have hb_ge : S ≤ min (σ.inv qstar wε + Qbar) 1 := le_min hS_le hS_hi
  have hb_pay : (qstar * P.θL - wε) * S ≤
      max ((qstar * P.θH - wε) * min P.αb (σ.inv qstar wε + Qbar))
        ((qstar * P.θL - wε) * min (σ.inv qstar wε + Qbar) 1) :=
    le_trans (mul_le_mul_of_nonneg_left hb_ge (sub_pos.mpr hwε_lt_L).le) (le_max_right _ _)
  rw [hg_eq] at hlb
  have hquad := ub_quad_os_p2 P (S := S) (q := qstar) (w := wstar) hk hDS
  have hvos_eq : P.ρ * ((qstar * P.θH - wstar) * P.αg) +
      (1 - P.ρ) * ((qstar * P.θL - wstar) * S) = P.V_OS Qbar := by
    rw [hquad, hc_qs]; unfold Params.V_OS; dsimp [qstar, wstar, S]; ring
  have hrv_ge : P.V_OS Qbar - (P.ρ * P.αg + (1 - P.ρ) * S) * ε ≤ σ.retailerValue P qstar wε := by
    have := mul_le_mul_of_nonneg_left hb_pay h1ρ.le
    dsimp [wε] at hlb this ⊢
    linarith
  have hε_bd : (P.ρ * P.αg + (1 - P.ρ) * S) * ε ≤ (P.V_OS Qbar - σ.retailerValue P σ.q σ.w) / 2 := by
    have := mul_le_mul_of_nonneg_left hε3 hDS.le
    dsimp [δ3] at this
    have heq : (P.ρ * P.αg + (1 - P.ρ) * S) *
        ((P.V_OS Qbar - σ.retailerValue P σ.q σ.w) / (2 * (P.ρ * P.αg + (1 - P.ρ) * S))) =
        (P.V_OS Qbar - σ.retailerValue P σ.q σ.w) / 2 := by field_simp [hDS.ne']
    linarith
  linarith [hropt qstar wε hqs_pos.le hwε0]

private lemma lb_voo_p2 (P : Params) (hStand : P.Standing) (hFocus : P.Focus)
    {Qbar : ℝ} (hQ0 : 0 ≤ Qbar) {σ : Profile} (hSPE : IsSPE P Qbar σ) :
    P.V_OO ≤ σ.retailerValue P σ.q σ.w := by
  rcases le_or_gt (1 - P.αg) Qbar with hQhi | hQmed
  · exact le_trans (voo_lt_vos_top_p2 P hStand hFocus).le
      (le_trans (vos_mono_p2 P hStand hFocus (sub_nonneg.mpr hStand.2.2.2.2.2.2.2.2.le) hQhi)
        (lb_vos_p2 P hStand hFocus hQ0 hSPE))
  · rcases hSPE with ⟨hpost, hinv, _, _, hropt⟩
    obtain ⟨hθH, hαg0, _, _, h1ρ, hD1, _, _, _⟩ := standing_focus_p2 P hStand hFocus
    rcases hStand with ⟨hθL, hθLH, hk, hρ0, hρ1, hαb0, hαb_lt, hαg_gt, hαg1⟩
    have hStand' : P.Standing := ⟨hθL, hθLH, hk, hρ0, hρ1, hαb0, hαb_lt, hαg_gt, hαg1⟩
    obtain ⟨_, hX_pos, _, hX_lt, _⟩ := y_props_p2 P hStand' hFocus hαg1.le (le_refl 1)
    obtain ⟨_, _, hX_le_YS, _, hYS_f⟩ :=
      y_props_p2 P hStand' hFocus (by linarith : P.αg ≤ P.αg + Qbar) (by linarith)
    let S_Q := P.αg + Qbar
    let qstar := (1 - P.ρ) * P.X / (2 * P.k)
    let wstar := (1 - P.ρ) * P.X ^ 2 / (4 * P.k)
    have hqs_pos : 0 < qstar := div_pos (mul_pos h1ρ hX_pos) (by linarith)
    have hws_pos : 0 < wstar := div_pos (mul_pos h1ρ (pow_pos hX_pos 2)) (by linarith)
    have hc1ρ : P.cost qstar / (1 - P.ρ) = wstar := by
      dsimp [qstar, wstar]; unfold Params.cost; field_simp [hk.ne', h1ρ.ne']; ring
    have hc_lt_ws : P.cost qstar < wstar := by
      rw [← hc1ρ, lt_div_iff₀ h1ρ]
      have hc_pos : 0 < P.cost qstar := mul_pos hk (pow_pos hqs_pos 2)
      have : P.cost qstar * (1 - P.ρ) < P.cost qstar * 1 := mul_lt_mul_of_pos_left (by linarith) hc_pos
      linarith
    have hws_lt_L : wstar < qstar * P.θL := by
      dsimp [qstar, wstar]
      rw [div_mul_eq_mul_div, div_lt_div_iff₀ (by linarith : 0 < 4 * P.k) (by linarith : 0 < 2 * P.k)]
      have := mul_lt_mul_of_pos_left hX_lt (mul_pos (mul_pos h1ρ hX_pos) hk)
      unfold Params.X
      linarith
    have hlow_qs : (qstar * P.θH - wstar) * P.αb < (qstar * P.θL - wstar) * S_Q := by
      dsimp [qstar, wstar]
      have hid1 : (1 - P.ρ) * P.X / (2 * P.k) * P.θH - (1 - P.ρ) * P.X ^ 2 / (4 * P.k) =
          (1 - P.ρ) * P.X / (4 * P.k) * (2 * P.θH - P.X) := by field_simp [hk.ne']; ring
      have hid2 : (1 - P.ρ) * P.X / (2 * P.k) * P.θL - (1 - P.ρ) * P.X ^ 2 / (4 * P.k) =
          (1 - P.ρ) * P.X / (4 * P.k) * (2 * P.θL - P.X) := by field_simp [hk.ne']; ring
      rw [hid1, hid2]
      have hfac : 0 < (1 - P.ρ) * P.X / (4 * P.k) := div_pos (mul_pos h1ρ hX_pos) (by linarith)
      have hSab : 0 < S_Q - P.αb := by dsimp [S_Q]; linarith [lt_of_mul_lt_mul_right (lt_trans hαb_lt hαg_gt) hθH.le]
      have hXf : P.X * (S_Q - P.αb) < 2 * (P.θL * S_Q - P.θH * P.αb) :=
        lt_of_le_of_lt (mul_le_mul_of_nonneg_right hX_le_YS hSab.le) hYS_f
      have hlt_inner : (2 * P.θH - P.X) * P.αb < (2 * P.θL - P.X) * S_Q := by dsimp [S_Q] at *; linarith
      have := mul_lt_mul_of_pos_left hlt_inner hfac
      linarith
    by_contra hlt_c
    have hgap : 0 < P.V_OO - σ.retailerValue P σ.q σ.w := sub_pos.mpr (lt_of_not_ge hlt_c)
    let δ1 := (qstar * P.θL - wstar) * S_Q - (qstar * P.θH - wstar) * P.αb
    let δ2 := qstar * P.θL - wstar
    let δ3 := (P.V_OO - σ.retailerValue P σ.q σ.w) / (2 * (P.ρ * P.αg + 1 - P.ρ))
    have hδ1 : 0 < δ1 := sub_pos.mpr hlow_qs
    have hδ2 : 0 < δ2 := sub_pos.mpr hws_lt_L
    have hδ3 : 0 < δ3 := div_pos hgap (mul_pos (by norm_num) hD1)
    let ε := min (min (δ1 / 2) (δ2 / 2)) δ3
    have hε_pos : 0 < ε := lt_min (lt_min (half_pos hδ1) (half_pos hδ2)) hδ3
    have hε1 : ε ≤ δ1 / 2 := le_trans (min_le_left _ _) (min_le_left _ _)
    have hε2 : ε ≤ δ2 / 2 := le_trans (min_le_left _ _) (min_le_right _ _)
    have hε3 : ε ≤ δ3 := min_le_right _ _
    let wε := wstar + ε
    have hwε_gt_c : P.cost qstar < wε := lt_trans hc_lt_ws (by dsimp [wε]; linarith)
    have hwε_gt_c1ρ : P.cost qstar / (1 - P.ρ) < wε := by rw [hc1ρ]; dsimp [wε]; linarith
    have hwε0 : 0 ≤ wε := (lt_trans hws_pos (by dsimp [wε]; linarith)).le
    have hwε_lt_L : wε < qstar * P.θL := by dsimp [wε, δ2] at *; linarith
    have hwε_lt_H : wε < qstar * P.θH := lt_trans hwε_lt_L (mul_lt_mul_of_pos_left hθLH hqs_pos)
    have hlow_ε : (qstar * P.θH - wε) * P.αb < (qstar * P.θL - wε) * S_Q := by
      have : ε * (S_Q - P.αb) ≤ ε := mul_le_of_le_one_right hε_pos.le (by dsimp [S_Q]; linarith)
      dsimp [wε, δ1] at *; linarith
    obtain ⟨hIε0, hIε_opt⟩ := hinv qstar wε hqs_pos.le hwε0
    have hresp := (supplier_response_medium P hStand' Qbar hQ0 hQmed σ hpost qstar wε hqs_pos
      hwε_gt_c hlow_ε).2.1 hwε_gt_c1ρ
    have hmem : σ.inv qstar wε ∈ ({1 - Qbar} : Set ℝ) := by
      rw [← hresp]; exact ⟨hIε0, hIε_opt⟩
    have hIε_eq : σ.inv qstar wε = 1 - Qbar := Set.mem_singleton_iff.mp hmem
    have hlb := rv_lb_strict_w_p2 P hStand' hQ0 σ hpost hqs_pos hwε_gt_c hwε_lt_H hIε0
    rw [hIε_eq, sub_add_cancel, min_eq_left hαg1.le, min_self] at hlb
    have hb_pay : qstar * P.θL - wε ≤
        max ((qstar * P.θH - wε) * min P.αb 1) ((qstar * P.θL - wε) * 1) :=
      le_trans (by ring_nf; exact le_refl _) (le_max_right _ _)
    have hvoo_eq : P.ρ * ((qstar * P.θH - wstar) * P.αg) +
        (1 - P.ρ) * (qstar * P.θL - wstar) = P.V_OO := by
      dsimp [qstar, wstar]
      unfold Params.V_OO Params.X Params.Y
      have hd : P.ρ * P.αg + (1 - P.ρ) * 1 = P.ρ * P.αg + 1 - P.ρ := by ring
      rw [hd]; field_simp [hk.ne', hD1.ne']; ring
    have hrv_ge : P.V_OO - (P.ρ * P.αg + 1 - P.ρ) * ε ≤ σ.retailerValue P qstar wε := by
      have := mul_le_mul_of_nonneg_left hb_pay h1ρ.le
      dsimp [wε] at hlb this ⊢
      linarith
    have hε_bd : (P.ρ * P.αg + 1 - P.ρ) * ε ≤ (P.V_OO - σ.retailerValue P σ.q σ.w) / 2 := by
      have := mul_le_mul_of_nonneg_left hε3 hD1.le
      dsimp [δ3] at this
      have heq : (P.ρ * P.αg + 1 - P.ρ) *
          ((P.V_OO - σ.retailerValue P σ.q σ.w) / (2 * (P.ρ * P.αg + 1 - P.ρ))) =
          (P.V_OO - σ.retailerValue P σ.q σ.w) / 2 := by field_simp [hD1.ne']
      linarith
    linarith [hropt qstar wε hqs_pos.le hwε0]

private lemma inv_ge_min_ab_p2 (P : Params) (hStand : P.Standing) {Qbar : ℝ} (hQ0 : 0 ≤ Qbar)
    (σ : Profile) (hpost : IsPostInventorySPE P Qbar σ)
    {q w : ℝ} (hq_pos : 0 < q) (hc_lt_w : P.cost q < w) (hwH : w < q * P.θH)
    (hI0 : 0 ≤ σ.inv q w)
    (hI_opt : ∀ I' : ℝ, 0 ≤ I' → σ.supplierValue P q w I' ≤ σ.supplierValue P q w (σ.inv q w)) :
    min P.αg (P.αb + Qbar) ≤ σ.inv q w + Qbar := by
  rcases hStand with ⟨hθL, hθLH, hk, hρ0, hρ1, hαb0, hαb_lt, hαg_gt, hαg1⟩
  have hStand' : P.Standing := ⟨hθL, hθLH, hk, hρ0, hρ1, hαb0, hαb_lt, hαg_gt, hαg1⟩
  have hθH : 0 < P.θH := lt_trans hθL hθLH
  have hαb_αg : P.αb < P.αg := lt_of_mul_lt_mul_right (lt_trans hαb_lt hαg_gt) hθH.le
  have h1ρ : 0 < 1 - P.ρ := sub_pos.mpr hρ1
  have hwc : 0 < w - P.cost q := sub_pos.mpr hc_lt_w
  let I := σ.inv q w
  by_contra hc
  have hlt : I + Qbar < min P.αg (P.αb + Qbar) := lt_of_not_ge hc
  let J₁ := min (P.αg - Qbar) P.αb
  have hJ₁Q : J₁ + Qbar = min P.αg (P.αb + Qbar) := by
    dsimp [J₁]
    rcases le_or_gt (P.αg - Qbar) P.αb with h1 | h1
    · rw [min_eq_left h1, min_eq_left (by linarith)]; ring
    · rw [min_eq_right h1.le, min_eq_right (by linarith)]
  have hI_lt_J₁ : I < J₁ := by linarith
  have hJ₁0 : 0 ≤ J₁ := le_trans hI0 hI_lt_J₁.le
  have hJ₁_ab : J₁ ≤ P.αb := min_le_right _ _
  have hJ₁Q_lo : P.αb ≤ J₁ + Qbar := by rw [hJ₁Q]; exact le_min hαb_αg.le (by linarith)
  have hJ₁Q_hi : J₁ + Qbar ≤ P.αg := by rw [hJ₁Q]; exact min_le_left _ _
  have hsv_J₁ : P.ρ * (w - P.cost q) * (J₁ + Qbar) + (1 - P.ρ) * (w - P.cost q) * P.αb ≤
      σ.supplierValue P q w J₁ := by
    have hbds := (sv_bounds_strict_w_p2 P hStand' hQ0 σ hpost hq_pos hc_lt_w hwH hJ₁0).1
    unfold fh_p2 at hbds
    rw [min_eq_right hJ₁Q_hi, max_eq_right (by linarith : J₁ ≤ J₁ + Qbar),
      min_eq_left hJ₁Q_lo, max_eq_right hJ₁_ab] at hbds
    linarith
  obtain ⟨hrm_I, _, hRg_I, hRb_lo, hRb_hi, hH_I, _⟩ :=
    active_strict_w_p2 P hStand' hQ0 σ hpost hq_pos hc_lt_w hwH hI0
  have hIQ_lt_ag : I + Qbar < P.αg := lt_of_lt_of_le hlt (min_le_left _ _)
  rcases le_or_gt (I + Qbar) P.αb with hIQ_ab | hIQ_gt_ab
  · have hRb_eq : σ.recv q w I .bad (σ.order q w I .bad) = I + Qbar :=
      le_antisymm (le_trans hRb_hi (min_le_left _ _))
        (by rwa [min_eq_right hIQ_ab] at hRb_lo)
    have hsv_I : σ.supplierValue P q w I = (w - P.cost q) * (I + Qbar) := by
      unfold Profile.supplierValue Profile.supplierStateValue Params.supplierState Params.prob
      rw [(hrm_I .good _).2, ← (hrm_I .good _).1, hRg_I, min_eq_right hIQ_lt_ag.le,
        max_eq_right (by linarith : I ≤ I + Qbar), (hrm_I .bad _).2, ← (hrm_I .bad _).1,
        hRb_eq, max_eq_right (by linarith : I ≤ I + Qbar)]
      ring
    have h1 := mul_lt_mul_of_pos_left hlt (mul_pos hρ0 hwc)
    have h2 := mul_le_mul_of_nonneg_left hIQ_ab (mul_pos h1ρ hwc).le
    have hopt := hI_opt J₁ hJ₁0
    rw [hsv_I] at hopt
    rw [← hJ₁Q] at h1
    linarith
  · by_cases hH_cond : (q * P.θL - w) * min (I + Qbar) 1 < (q * P.θH - w) * min P.αb (I + Qbar)
    · have hsv_I := (sv_bounds_strict_w_p2 P hStand' hQ0 σ hpost hq_pos hc_lt_w hwH hI0).2.2.1 hH_cond
      unfold fh_p2 at hsv_I
      rw [min_eq_right hIQ_lt_ag.le, max_eq_right (by linarith : I ≤ I + Qbar),
        min_eq_left hIQ_gt_ab.le, max_eq_right (le_trans hI_lt_J₁.le hJ₁_ab)] at hsv_I
      have h1 := mul_lt_mul_of_pos_left (by rw [hJ₁Q]; exact hlt : I + Qbar < J₁ + Qbar)
        (mul_pos hρ0 hwc)
      have hopt := hI_opt J₁ hJ₁0
      rw [hsv_I] at hopt
      linarith
    · have hge_L : (q * P.θH - w) * P.αb ≤ (q * P.θL - w) * (I + Qbar) := by
        have hnot := le_of_not_gt hH_cond
        rwa [min_eq_left hIQ_gt_ab.le, min_eq_left (le_trans hIQ_lt_ag.le hαg1.le)] at hnot
      have hwL_pos : 0 < q * P.θL - w :=
        pos_of_mul_pos_left (lt_of_lt_of_le (mul_pos (sub_pos.mpr hwH) hαb0) hge_L)
          (lt_trans hαb0 hIQ_gt_ab).le
      let J₂ := P.αg - Qbar
      have hJ₂0 : 0 ≤ J₂ := by dsimp [J₂]; linarith
      have hJ₂Q : J₂ + Qbar = P.αg := sub_add_cancel P.αg Qbar
      have hL_J₂ : (q * P.θH - w) * min P.αb (J₂ + Qbar) < (q * P.θL - w) * min (J₂ + Qbar) 1 := by
        rw [hJ₂Q, min_eq_left hαb_αg.le, min_eq_left hαg1.le]
        exact lt_of_le_of_lt hge_L (mul_lt_mul_of_pos_left hIQ_lt_ag hwL_pos)
      have hsv_J₂ := (sv_bounds_strict_w_p2 P hStand' hQ0 σ hpost hq_pos hc_lt_w hwH hJ₂0).2.2.2 hL_J₂
      unfold fl_p2 at hsv_J₂
      rw [hJ₂Q, min_self, min_eq_left hαg1.le, max_eq_right (by dsimp [J₂]; linarith : J₂ ≤ P.αg)] at hsv_J₂
      have hsv_I_ub := (sv_bounds_strict_w_p2 P hStand' hQ0 σ hpost hq_pos hc_lt_w hwH hI0).2.1
      unfold fl_p2 at hsv_I_ub
      rw [min_eq_right hIQ_lt_ag.le, min_eq_left (le_trans hIQ_lt_ag.le hαg1.le),
        max_eq_right (by linarith : I ≤ I + Qbar)] at hsv_I_ub
      have hlt_ag : (w - P.cost q) * (I + Qbar) < (w - P.cost q) * P.αg :=
        mul_lt_mul_of_pos_left hIQ_lt_ag hwc
      have hopt := hI_opt J₂ hJ₂0
      linarith

private lemma lb_vhos_p2 (P : Params) (hStand : P.Standing)
    {Qbar : ℝ} (hQ0 : 0 ≤ Qbar) {σ : Profile} (hSPE : IsSPE P Qbar σ) :
    (P.ρ * min P.αg (P.αb + Qbar) + (1 - P.ρ) * P.αb) * P.θH ^ 2 / (4 * P.k) ≤
      σ.retailerValue P σ.q σ.w := by
  rcases hSPE with ⟨hpost, hinv, _, _, hropt⟩
  rcases hStand with ⟨hθL, hθLH, hk, hρ0, hρ1, hαb0, hαb_lt, hαg_gt, hαg1⟩
  have hStand' : P.Standing := ⟨hθL, hθLH, hk, hρ0, hρ1, hαb0, hαb_lt, hαg_gt, hαg1⟩
  have hθH : 0 < P.θH := lt_trans hθL hθLH
  have hαb_αg : P.αb < P.αg := lt_of_mul_lt_mul_right (lt_trans hαb_lt hαg_gt) hθH.le
  have h1ρ : 0 < 1 - P.ρ := sub_pos.mpr hρ1
  let A := P.ρ * min P.αg (P.αb + Qbar) + (1 - P.ρ) * P.αb
  have hA_pos : 0 < A :=
    add_pos (mul_pos hρ0 (lt_min (lt_trans hαb0 hαb_αg) (by linarith))) (mul_pos h1ρ hαb0)
  let V_H := A * P.θH ^ 2 / (4 * P.k)
  change V_H ≤ σ.retailerValue P σ.q σ.w
  by_contra hlt_c
  have hgap : 0 < V_H - σ.retailerValue P σ.q σ.w := sub_pos.mpr (lt_of_not_ge hlt_c)
  let qstar := P.θH / (2 * P.k)
  let wstar := P.θH ^ 2 / (4 * P.k)
  have hqs_pos : 0 < qstar := div_pos hθH (by linarith)
  have hws_pos : 0 < wstar := div_pos (pow_pos hθH 2) (by linarith)
  have hc_qs : P.cost qstar = wstar := by
    dsimp [qstar, wstar]; unfold Params.cost; field_simp [hk.ne']; ring
  have hws_lt_H : wstar < qstar * P.θH := by
    dsimp [qstar, wstar]; field_simp [hk.ne']
    have : P.θH ^ 2 * 1 < P.θH ^ 2 * 2 := mul_lt_mul_of_pos_left (by norm_num) (pow_pos hθH 2)
    linarith
  let ε := min ((qstar * P.θH - wstar) / 2) ((V_H - σ.retailerValue P σ.q σ.w) / (2 * A))
  have hε_pos : 0 < ε := lt_min (half_pos (sub_pos.mpr hws_lt_H))
    (div_pos hgap (mul_pos (by norm_num) hA_pos))
  let wε := wstar + ε
  have hwε_gt_c : P.cost qstar < wε := by rw [hc_qs]; dsimp [wε]; linarith
  have hwε0 : 0 ≤ wε := (lt_trans hws_pos (by dsimp [wε]; linarith)).le
  have hwε_lt_H : wε < qstar * P.θH := by
    have := min_le_left ((qstar * P.θH - wstar) / 2) ((V_H - σ.retailerValue P σ.q σ.w) / (2 * A))
    dsimp [wε, ε] at *; linarith
  obtain ⟨hIε0, hIε_opt⟩ := hinv qstar wε hqs_pos.le hwε0
  have hIQ_ge := inv_ge_min_ab_p2 P hStand' hQ0 σ hpost hqs_pos hwε_gt_c hwε_lt_H hIε0 hIε_opt
  have hlb := rv_lb_strict_w_p2 P hStand' hQ0 σ hpost hqs_pos hwε_gt_c hwε_lt_H hIε0
  have hg_ge : min P.αg (P.αb + Qbar) ≤ min P.αg (σ.inv qstar wε + Qbar) :=
    le_min (min_le_left _ _) hIQ_ge
  have hb_eq : min P.αb (σ.inv qstar wε + Qbar) = P.αb :=
    min_eq_left (le_trans (le_min hαb_αg.le (by linarith : P.αb ≤ P.αb + Qbar)) hIQ_ge)
  have hqsH : qstar * P.θH - wstar = wstar := by
    dsimp [qstar, wstar]; field_simp [hk.ne']; ring
  have hVH_eq : A * (qstar * P.θH - wstar) = V_H := by
    rw [hqsH]; dsimp [V_H, wstar]; ring
  have hg_pay : (qstar * P.θH - wε) * min P.αg (P.αb + Qbar) ≤
      (qstar * P.θH - wε) * min P.αg (σ.inv qstar wε + Qbar) :=
    mul_le_mul_of_nonneg_left hg_ge (sub_pos.mpr hwε_lt_H).le
  have hb_pay : (qstar * P.θH - wε) * P.αb ≤
      max ((qstar * P.θH - wε) * min P.αb (σ.inv qstar wε + Qbar))
        ((qstar * P.θL - wε) * min (σ.inv qstar wε + Qbar) 1) := by
    rw [hb_eq]; exact le_max_left _ _
  have hrv_ge : V_H - A * ε ≤ σ.retailerValue P qstar wε := by
    have := mul_le_mul_of_nonneg_left hg_pay hρ0.le
    have := mul_le_mul_of_nonneg_left hb_pay h1ρ.le
    dsimp [A, wε] at hVH_eq hlb this ⊢
    linarith
  have hε_bd : A * ε ≤ (V_H - σ.retailerValue P σ.q σ.w) / 2 := by
    have h2 := min_le_right ((qstar * P.θH - wstar) / 2) ((V_H - σ.retailerValue P σ.q σ.w) / (2 * A))
    have := mul_le_mul_of_nonneg_left h2 hA_pos.le
    have heq : A * ((V_H - σ.retailerValue P σ.q σ.w) / (2 * A)) =
        (V_H - σ.retailerValue P σ.q σ.w) / 2 := by field_simp [hA_pos.ne']
    dsimp [ε] at *; linarith
  linarith [hropt qstar wε hqs_pos.le hwε0]

private lemma active_rv_ub_p2 (P : Params) (hStand : P.Standing) {Qbar : ℝ} (hQ0 : 0 ≤ Qbar)
    (σ : Profile) (hpost : IsPostInventorySPE P Qbar σ)
    {q w : ℝ} (hq_pos : 0 < q) (hw0 : 0 ≤ w) (hwH : w < q * P.θH) (hI0 : 0 ≤ σ.inv q w) :
    (σ.inv q w + Qbar = 0 → σ.retailerValue P q w = 0) ∧
    (0 < σ.inv q w + Qbar →
      σ.retailerValue P q w ≤
        P.ρ * ((q * P.θH - w) * min P.αg (σ.inv q w + Qbar)) +
          (1 - P.ρ) * max ((q * P.θH - w) * min P.αb (σ.inv q w + Qbar))
            ((q * P.θL - w) * min (σ.inv q w + Qbar) 1)) := by
  rcases hStand with ⟨hθL, hθLH, hk, hρ0, hρ1, hαb0, hαb_lt, hαg_gt, hαg1⟩
  have hStand' : P.Standing := ⟨hθL, hθLH, hk, hρ0, hρ1, hαb0, hαb_lt, hαg_gt, hαg1⟩
  have hθH : 0 < P.θH := lt_trans hθL hθLH
  have hαg0 : 0 < P.αg := pos_of_mul_pos_left (lt_trans hθL hαg_gt) hθH.le
  have hαb_αg : P.αb < P.αg := lt_of_mul_lt_mul_right (lt_trans hαb_lt hαg_gt) hθH.le
  have hαb1 : P.αb < 1 := lt_trans hαb_αg hαg1
  have h1ρ : 0 < 1 - P.ρ := sub_pos.mpr hρ1
  have hwH0 : 0 < q * P.θH - w := sub_pos.mpr hwH
  let I := σ.inv q w
  let S := I + Qbar
  have hmb : ∀ s : State, ∀ Q : ℝ, 0 ≤ Q →
      0 ≤ σ.made q w I s Q ∧ σ.made q w I s Q ≤ Qbar ∧
      0 ≤ σ.recv q w I s Q ∧ σ.recv q w I s Q ≤ S := by
    intro s Q hQ
    unfold Profile.made Profile.recv inSeason received
    rcases le_or_gt Q I with hQI | hIQ
    · rw [if_pos hQI, if_pos hQI]; exact ⟨le_refl 0, hQ0, hQ, by dsimp [S]; linarith⟩
    · rw [if_neg (not_le_of_gt hIQ), if_neg (not_le_of_gt hIQ)]
      obtain ⟨hr0, hrQ, _⟩ := hpost.2.1 q w I s Q hq_pos.le hw0 hI0 hIQ
      exact ⟨hr0, hrQ, le_min (add_nonneg hI0 hr0) hQ,
        le_trans (min_le_left _ _) (by dsimp [S]; linarith)⟩
  let Qg := σ.order q w I .good
  let Qb := σ.order q w I .bad
  obtain ⟨hQg0, _⟩ := hpost.2.2 q w I .good hq_pos.le hw0 hI0
  obtain ⟨hQb0, _⟩ := hpost.2.2 q w I .bad hq_pos.le hw0 hI0
  obtain ⟨hmg0, hmgQ, hRg0, hRgS⟩ := hmb .good Qg hQg0
  obtain ⟨hmb0, hmbQ, hRb0, hRbS⟩ := hmb .bad Qb hQb0
  obtain ⟨hpg0, _⟩ := hpost.1 q w I .good Qg _ hq_pos.le hw0 hI0 hQg0 hmg0 hmgQ
  obtain ⟨hpb0, _⟩ := hpost.1 q w I .bad Qb _ hq_pos.le hw0 hI0 hQb0 hmb0 hmbQ
  refine ⟨fun hS0 => ?_, fun hS_pos => ?_⟩
  · have hRg0' : σ.recv q w I .good Qg = 0 := le_antisymm (by linarith) hRg0
    have hRb0' : σ.recv q w I .bad Qb = 0 := le_antisymm (by linarith) hRb0
    have hov0 : ∀ s : State, σ.orderValue P q w I s (σ.order q w I s) = 0 := by
      rintro (_ | _)
      · unfold Profile.orderValue Params.retailerState
        have hd0 : 0 ≤ P.demand q P.αg (σ.priceAfter q w I .good Qg) := by
          unfold Params.demand; split_ifs <;> linarith
        rw [Params.alpha, hRg0', min_eq_right hd0, mul_zero, mul_zero, sub_zero]
      · unfold Profile.orderValue Params.retailerState
        have hd0 : 0 ≤ P.demand q P.αb (σ.priceAfter q w I .bad Qb) := by
          unfold Params.demand; split_ifs <;> linarith
        rw [Params.alpha, hRb0', min_eq_right hd0, mul_zero, mul_zero, sub_zero]
    unfold Profile.retailerValue Params.prob
    change P.ρ * σ.orderValue P q w I .good Qg + (1 - P.ρ) * σ.orderValue P q w I .bad Qb = 0
    rw [hov0 .good, hov0 .bad]; ring
  · have hrule := retailer_stage_rule P hStand' q w S hq_pos hw0 hwH hS_pos.le
    have hov_g : σ.orderValue P q w I .good Qg ≤ (q * P.θH - w) * min P.αg S := by
      have hstep : σ.orderValue P q w I .good Qg =
          P.stepOnePayoff q w P.αg S (σ.recv q w I .good Qg) (σ.priceAfter q w I .good Qg) := by
        unfold Profile.orderValue Params.retailerState Params.stepOnePayoff Params.alpha
        rw [min_eq_left hRgS]
      rw [hstep]
      have h1 := (hrule.1 P.αg hαg0.le hαg1.le).2 ⟨_, _, hRg0, hpg0, rfl⟩
      have hvH0 : 0 ≤ (q * P.θH - w) * min P.αg S := mul_nonneg hwH0.le (le_min hαg0.le hS_pos.le)
      have hvL_le : (q * P.θL - w) * min S 1 ≤ (q * P.θH - w) * min P.αg S := by
        rcases le_or_gt (q * P.θL - w) 0 with hL0 | hL_pos
        · exact le_trans (mul_nonpos_of_nonpos_of_nonneg hL0 (le_min hS_pos.le zero_le_one)) hvH0
        · rcases le_or_gt S P.αg with hSα | hSα
          · rw [min_eq_left (le_trans hSα hαg1.le), min_eq_right hSα]
            exact mul_le_mul_of_nonneg_right
              (by have := mul_lt_mul_of_pos_left hθLH hq_pos; linarith) hS_pos.le
          · rw [min_eq_left hSα.le]
            have hle1 : (q * P.θL - w) * min S 1 ≤ q * P.θL - w := by
              have := mul_le_mul_of_nonneg_left (min_le_right S 1) hL_pos.le; linarith
            have h2 : q * P.θL < q * (P.αg * P.θH) := mul_lt_mul_of_pos_left hαg_gt hq_pos
            have h3 : w * P.αg ≤ w := by have := mul_le_mul_of_nonneg_left hαg1.le hw0; linarith
            linarith
      rwa [max_eq_left hvL_le, max_eq_left hvH0] at h1
    have hov_b : σ.orderValue P q w I .bad Qb ≤
        max ((q * P.θH - w) * min P.αb S) ((q * P.θL - w) * min S 1) := by
      have hstep : σ.orderValue P q w I .bad Qb =
          P.stepOnePayoff q w P.αb S (σ.recv q w I .bad Qb) (σ.priceAfter q w I .bad Qb) := by
        unfold Profile.orderValue Params.retailerState Params.stepOnePayoff Params.alpha
        rw [min_eq_left hRbS]
      rw [hstep]
      have h1 := (hrule.1 P.αb hαb0.le hαb1.le).2 ⟨_, _, hRb0, hpb0, rfl⟩
      have hvH0 : 0 ≤ (q * P.θH - w) * min P.αb S := mul_nonneg hwH0.le (le_min hαb0.le hS_pos.le)
      rwa [max_eq_left (le_trans hvH0 (le_max_left _ _))] at h1
    unfold Profile.retailerValue Params.prob
    change P.ρ * σ.orderValue P q w I .good Qg + (1 - P.ρ) * σ.orderValue P q w I .bad Qb ≤ _
    have := mul_le_mul_of_nonneg_left hov_g hρ0.le
    have := mul_le_mul_of_nonneg_left hov_b h1ρ.le
    linarith

private lemma w_eq_cost_inv_le_ag_p2 (P : Params) (hStand : P.Standing) {Qbar : ℝ} (hQ0 : 0 ≤ Qbar)
    (σ : Profile) (hpost : IsPostInventorySPE P Qbar σ)
    {q w : ℝ} (hq_pos : 0 < q) (hw_eq : w = P.cost q) (hwH : w < q * P.θH)
    (hI0 : 0 ≤ σ.inv q w) (hsv_nn : 0 ≤ σ.supplierValue P q w (σ.inv q w)) :
    σ.inv q w ≤ P.αg := by
  rcases hStand with ⟨hθL, hθLH, hk, hρ0, hρ1, hαb0, hαb_lt, hαg_gt, hαg1⟩
  have hStand' : P.Standing := ⟨hθL, hθLH, hk, hρ0, hρ1, hαb0, hαb_lt, hαg_gt, hαg1⟩
  have hθH : 0 < P.θH := lt_trans hθL hθLH
  have hαg0 : 0 < P.αg := pos_of_mul_pos_left (lt_trans hθL hαg_gt) hθH.le
  have hw_pos : 0 < w := by rw [hw_eq]; exact mul_pos hk (pow_pos hq_pos 2)
  have hqLH : q * P.θL < q * P.θH := mul_lt_mul_of_pos_left hθLH hq_pos
  let I := σ.inv q w
  by_contra hc
  have hI_gt : P.αg < I := lt_of_not_ge hc
  have hI_le_Rg := ((w_le_cost_props_p2 P hStand' hQ0 σ hpost hq_pos.le hw_pos.le hI0 hsv_nn
    hw_eq.le).2 hw_eq hq_pos).1
  have hRg_gt : P.αg < σ.recv q w I .good (σ.order q w I .good) := lt_of_lt_of_le hI_gt hI_le_Rg
  have h1 := (hpost.2.2 q w I .good hq_pos.le hw_pos.le hI0).2 P.αg hαg0.le
  have hm0 : σ.made q w I .good P.αg = 0 := by unfold Profile.made inSeason; rw [if_pos hI_gt.le]
  have hrec_ag : σ.recv q w I .good P.αg = P.αg := by unfold Profile.recv received; rw [if_pos hI_gt.le]
  have hp_opt := (hpost.1 q w I .good P.αg (σ.made q w I .good P.αg) hq_pos.le hw_pos.le hI0 hαg0.le
    (by rw [hm0]) (by rw [hm0]; exact hQ0)).2 (q * P.θH) (mul_pos hq_pos hθH).le
  have hrm_ag : received I P.αg (σ.made q w I .good P.αg) = P.αg := by
    rw [hm0]; unfold received; rw [if_pos hI_gt.le]
  unfold Profile.orderValue Profile.priceAfter at h1
  rw [hrec_ag] at h1
  rw [hrm_ag] at hp_opt
  have hlhs : P.retailerState q w .good P.αg (q * P.θH) = (q * P.θH - w) * P.αg := by
    unfold Params.retailerState Params.demand Params.alpha
    rw [if_neg (not_le_of_gt hqLH), if_pos (le_refl _), zero_add, min_self]; ring
  rw [hlhs] at hp_opt
  have hov_ge : (q * P.θH - w) * P.αg ≤ σ.orderValue P q w I .good (σ.order q w I .good) :=
    le_trans hp_opt h1
  let Rg := σ.recv q w I .good (σ.order q w I .good)
  let pg := σ.priceAfter q w I .good (σ.order q w I .good)
  have hov_lt : σ.orderValue P q w I .good (σ.order q w I .good) < (q * P.θH - w) * P.αg := by
    unfold Profile.orderValue Params.retailerState Params.demand Params.alpha
    change pg * min ((if pg ≤ q * P.θL then 1 - P.αg else 0) +
        if pg ≤ q * P.θH then P.αg else 0) Rg - w * Rg < (q * P.θH - w) * P.αg
    rcases le_or_gt pg (q * P.θL) with hpL | hpL
    · rw [if_pos hpL, if_pos (le_trans hpL hqLH.le), sub_add_cancel]
      have hm0' : 0 ≤ min 1 Rg := le_min zero_le_one (lt_trans hαg0 hRg_gt).le
      have h_p_le : pg * min 1 Rg ≤ q * P.θL * min 1 Rg := mul_le_mul_of_nonneg_right hpL hm0'
      have h_w_le : w * min 1 Rg ≤ w * Rg := mul_le_mul_of_nonneg_left (min_le_right 1 Rg) hw_pos.le
      have h_m1 : (q * P.θL - w) * min 1 Rg ≤ max (q * P.θL - w) 0 := by
        rcases le_or_gt (q * P.θL - w) 0 with hL0 | hL0
        · exact le_trans (mul_nonpos_of_nonpos_of_nonneg hL0 hm0') (le_max_right _ _)
        · exact le_trans (by have := mul_le_mul_of_nonneg_left (min_le_left 1 Rg) hL0.le; linarith)
            (le_max_left _ _)
      have h2 : q * P.θL < q * (P.αg * P.θH) := mul_lt_mul_of_pos_left hαg_gt hq_pos
      have h3 : w * P.αg ≤ w := by have := mul_le_mul_of_nonneg_left hαg1.le hw_pos.le; linarith
      have hmax_lt : max (q * P.θL - w) 0 < (q * P.θH - w) * P.αg :=
        max_lt (by linarith) (mul_pos (sub_pos.mpr hwH) hαg0)
      linarith
    · rcases le_or_gt pg (q * P.θH) with hpH | hpH
      · rw [if_neg (not_le_of_gt hpL), if_pos hpH, zero_add, min_eq_left hRg_gt.le]
        have := mul_le_mul_of_nonneg_right hpH hαg0.le
        have := mul_lt_mul_of_pos_left hRg_gt hw_pos
        linarith
      · rw [if_neg (not_le_of_gt hpL), if_neg (not_le_of_gt hpH), add_zero,
          min_eq_left (lt_trans hαg0 hRg_gt).le, mul_zero]
        have := mul_pos hw_pos (lt_trans hαg0 hRg_gt)
        have := mul_pos (sub_pos.mpr hwH) hαg0
        linarith
  linarith

private lemma inv_le_ag_lt_oo_p2 (P : Params) (hStand : P.Standing)
    {Qbar : ℝ} (hQ0 : 0 ≤ Qbar) (hQ1 : Qbar < 1 - P.αg)
    (σ : Profile) (hpost : IsPostInventorySPE P Qbar σ)
    {q w : ℝ} (hq_pos : 0 < q) (hcw : P.cost q ≤ w) (hw_lt_c1ρ : w < P.cost q / (1 - P.ρ))
    (hwL : w < q * P.θL) (hI0 : 0 ≤ σ.inv q w)
    (hI_opt : ∀ I' : ℝ, 0 ≤ I' → σ.supplierValue P q w I' ≤ σ.supplierValue P q w (σ.inv q w))
    (hsv_nn : 0 ≤ σ.supplierValue P q w (σ.inv q w))
    (hBrL : (q * P.θH - w) * min P.αb (σ.inv q w + Qbar) <
      (q * P.θL - w) * min (σ.inv q w + Qbar) 1) :
    σ.inv q w ≤ P.αg := by
  rcases hStand with ⟨hθL, hθLH, hk, hρ0, hρ1, hαb0, hαb_lt, hαg_gt, hαg1⟩
  have hStand' : P.Standing := ⟨hθL, hθLH, hk, hρ0, hρ1, hαb0, hαb_lt, hαg_gt, hαg1⟩
  have hθH : 0 < P.θH := lt_trans hθL hθLH
  have hαg0 : 0 < P.αg := pos_of_mul_pos_left (lt_trans hθL hαg_gt) hθH.le
  have hαb_αg : P.αb < P.αg := lt_of_mul_lt_mul_right (lt_trans hαb_lt hαg_gt) hθH.le
  have h1ρ : 0 < 1 - P.ρ := sub_pos.mpr hρ1
  have hwH : w < q * P.θH := lt_trans hwL (mul_lt_mul_of_pos_left hθLH hq_pos)
  rcases eq_or_lt_of_le hcw with hweq | hc_lt_w
  · exact w_eq_cost_inv_le_ag_p2 P hStand' hQ0 σ hpost hq_pos hweq.symm hwH hI0 hsv_nn
  · let I := σ.inv q w
    by_contra hc
    have hI_gt : P.αg < I := lt_of_not_ge hc
    have hc_pos : 0 < P.cost q := mul_pos hk (pow_pos hq_pos 2)
    have hwL0 : 0 < q * P.θL - w := sub_pos.mpr hwL
    have hslope : (1 - P.ρ) * w - P.cost q < 0 := by
      have := (lt_div_iff₀' h1ρ).mp hw_lt_c1ρ; linarith
    let S0 := (q * P.θH - w) * P.αb / (q * P.θL - w)
    have hS0_lt : S0 < min (I + Qbar) 1 := by
      dsimp [S0]; rw [div_lt_iff₀ hwL0, mul_comm _ (q * P.θL - w)]
      rwa [min_eq_left (by linarith : P.αb ≤ I + Qbar)] at hBrL
    let J_lo := max P.αg (S0 - Qbar)
    let J_hi := min I (1 - Qbar)
    have hlo_hi : J_lo < J_hi := by
      have h1 := lt_of_lt_of_le hS0_lt (min_le_left _ _)
      have h2 := lt_of_lt_of_le hS0_lt (min_le_right _ _)
      exact max_lt (lt_min hI_gt (by linarith)) (lt_min (by linarith) (by linarith))
    let J' := (J_lo + J_hi) / 2
    have hlo_ag : P.αg ≤ J_lo := le_max_left P.αg (S0 - Qbar)
    have hlo_S0 : S0 - Qbar ≤ J_lo := le_max_right P.αg (S0 - Qbar)
    have hhi_I : J_hi ≤ I := min_le_left I (1 - Qbar)
    have hhi_1Q : J_hi ≤ 1 - Qbar := min_le_right I (1 - Qbar)
    have hJ'_ag : P.αg < J' := by change P.αg < (J_lo + J_hi) / 2; linarith
    have hJ'0 : 0 ≤ J' := (lt_trans hαg0 hJ'_ag).le
    have hJ'_lt_I : J' < I := by change (J_lo + J_hi) / 2 < I; linarith
    have hJ'_lt_1Q : J' < 1 - Qbar := by change (J_lo + J_hi) / 2 < 1 - Qbar; linarith
    have hS0_lt_J'Q : S0 < J' + Qbar := by change S0 < (J_lo + J_hi) / 2 + Qbar; linarith
    have hcmp_J' : (q * P.θH - w) * min P.αb (J' + Qbar) < (q * P.θL - w) * min (J' + Qbar) 1 := by
      rw [min_eq_left (by linarith : P.αb ≤ J' + Qbar), min_eq_left (by linarith : J' + Qbar ≤ 1)]
      have h1 : (q * P.θH - w) * P.αb = (q * P.θL - w) * S0 := by
        dsimp [S0]; rw [mul_div_cancel₀ _ hwL0.ne']
      rw [h1]; exact mul_lt_mul_of_pos_left hS0_lt_J'Q hwL0
    have hsv_J' := (sv_bounds_strict_w_p2 P hStand' hQ0 σ hpost hq_pos hc_lt_w hwH hJ'0).2.2.2 hcmp_J'
    have hsv_I := (sv_bounds_strict_w_p2 P hStand' hQ0 σ hpost hq_pos hc_lt_w hwH hI0).2.2.2 hBrL
    unfold fl_p2 at hsv_J' hsv_I
    rw [min_eq_left (by linarith : P.αg ≤ J' + Qbar), max_eq_left hJ'_ag.le,
      min_eq_left (by linarith : J' + Qbar ≤ 1), max_eq_right (by linarith : J' ≤ J' + Qbar)] at hsv_J'
    rw [min_eq_left (by linarith : P.αg ≤ I + Qbar), max_eq_left hI_gt.le] at hsv_I
    have hopt := hI_opt J' hJ'0
    rw [hsv_J', hsv_I] at hopt
    rcases le_or_gt I (1 - Qbar) with hIle | hIgt
    · rw [min_eq_left (by linarith : I + Qbar ≤ 1), max_eq_right (by linarith : I ≤ I + Qbar)] at hopt
      have := mul_lt_mul_of_neg_left hJ'_lt_I hslope
      linarith
    · rw [min_eq_right (by linarith : 1 ≤ I + Qbar)] at hopt
      have hg_lt : w * P.αg - P.cost q * I < w * P.αg - P.cost q * (1 - Qbar) := by
        have := mul_lt_mul_of_pos_left hIgt hc_pos; linarith
      have hb_le : w * 1 - P.cost q * max I 1 ≤ w * 1 - P.cost q * 1 := by
        have := mul_le_mul_of_nonneg_left (le_max_right I 1) hc_pos.le; linarith
      have := mul_lt_mul_of_pos_left hg_lt hρ0
      have := mul_le_mul_of_nonneg_left hb_le h1ρ.le
      have := mul_lt_mul_of_neg_left hJ'_lt_1Q hslope
      linarith

private lemma inv_le_ab_strictH_p2 (P : Params) (hStand : P.Standing) {Qbar : ℝ} (hQ0 : 0 ≤ Qbar)
    (σ : Profile) (hpost : IsPostInventorySPE P Qbar σ)
    {q w : ℝ} (hq_pos : 0 < q) (hcw : P.cost q ≤ w) (hw_lt_cρ : w < P.cost q / P.ρ)
    (hwH : w < q * P.θH) (hI0 : 0 ≤ σ.inv q w)
    (hI_opt : ∀ I' : ℝ, 0 ≤ I' → σ.supplierValue P q w I' ≤ σ.supplierValue P q w (σ.inv q w))
    (hsv_nn : 0 ≤ σ.supplierValue P q w (σ.inv q w))
    (hBrH : (q * P.θL - w) * min (σ.inv q w + Qbar) 1 <
      (q * P.θH - w) * min P.αb (σ.inv q w + Qbar)) :
    σ.inv q w ≤ P.αb := by
  rcases hStand with ⟨hθL, hθLH, hk, hρ0, hρ1, hαb0, hαb_lt, hαg_gt, hαg1⟩
  have hStand' : P.Standing := ⟨hθL, hθLH, hk, hρ0, hρ1, hαb0, hαb_lt, hαg_gt, hαg1⟩
  have hθH : 0 < P.θH := lt_trans hθL hθLH
  have hαb_αg : P.αb < P.αg := lt_of_mul_lt_mul_right (lt_trans hαb_lt hαg_gt) hθH.le
  have h1ρ : 0 < 1 - P.ρ := sub_pos.mpr hρ1
  have hc_pos : 0 < P.cost q := mul_pos hk (pow_pos hq_pos 2)
  have hw_pos : 0 < w := lt_of_lt_of_le hc_pos hcw
  have hqLH : q * P.θL < q * P.θH := mul_lt_mul_of_pos_left hθLH hq_pos
  let I := σ.inv q w
  by_contra hc
  have hI_gt : P.αb < I := lt_of_not_ge hc
  rcases eq_or_lt_of_le hcw with hweq | hc_lt_w
  · have hI_le_Rb := ((w_le_cost_props_p2 P hStand' hQ0 σ hpost hq_pos.le hw_pos.le hI0 hsv_nn
      hweq.symm.le).2 hweq.symm hq_pos).2
    let Qb := σ.order q w I .bad
    let Rb := σ.recv q w I .bad Qb
    let pb := σ.priceAfter q w I .bad Qb
    have hRb_gt : P.αb < Rb := lt_of_lt_of_le hI_gt hI_le_Rb
    have hRb_le_S : Rb ≤ I + Qbar := by
      dsimp only [Rb]
      unfold Profile.recv received
      rcases le_or_gt Qb I with h1 | h1
      · rw [if_pos h1]; linarith
      · rw [if_neg (not_le_of_gt h1)]
        obtain ⟨_, hrQ, _⟩ := hpost.2.1 q w I .bad Qb hq_pos.le hw_pos.le hI0 h1
        exact le_trans (min_le_left _ _) (by linarith)
    have h1 := (hpost.2.2 q w I .bad hq_pos.le hw_pos.le hI0).2 P.αb hαb0.le
    have hm0 : σ.made q w I .bad P.αb = 0 := by unfold Profile.made inSeason; rw [if_pos hI_gt.le]
    have hrec_ab : σ.recv q w I .bad P.αb = P.αb := by unfold Profile.recv received; rw [if_pos hI_gt.le]
    have hp_opt := (hpost.1 q w I .bad P.αb (σ.made q w I .bad P.αb) hq_pos.le hw_pos.le hI0 hαb0.le
      (by rw [hm0]) (by rw [hm0]; exact hQ0)).2 (q * P.θH) (mul_pos hq_pos hθH).le
    have hrm_ab : received I P.αb (σ.made q w I .bad P.αb) = P.αb := by
      rw [hm0]; unfold received; rw [if_pos hI_gt.le]
    unfold Profile.orderValue Profile.priceAfter at h1
    rw [hrec_ab] at h1
    rw [hrm_ab] at hp_opt
    have hlhs : P.retailerState q w .bad P.αb (q * P.θH) = (q * P.θH - w) * P.αb := by
      unfold Params.retailerState Params.demand Params.alpha
      rw [if_neg (not_le_of_gt hqLH), if_pos (le_refl _), zero_add, min_self]; ring
    rw [hlhs] at hp_opt
    have hov_ge : (q * P.θH - w) * P.αb ≤ σ.orderValue P q w I .bad Qb := le_trans hp_opt h1
    have hBrH' : (q * P.θL - w) * min (I + Qbar) 1 < (q * P.θH - w) * P.αb := by
      rwa [min_eq_left (by linarith : P.αb ≤ I + Qbar)] at hBrH
    have hov_lt : σ.orderValue P q w I .bad Qb < (q * P.θH - w) * P.αb := by
      unfold Profile.orderValue Params.retailerState Params.demand Params.alpha
      change pb * min ((if pb ≤ q * P.θL then 1 - P.αb else 0) +
          if pb ≤ q * P.θH then P.αb else 0) Rb - w * Rb < (q * P.θH - w) * P.αb
      rcases le_or_gt pb (q * P.θL) with hpL | hpL
      · rw [if_pos hpL, if_pos (le_trans hpL hqLH.le), sub_add_cancel]
        have hm0' : 0 ≤ min 1 Rb := le_min zero_le_one (lt_trans hαb0 hRb_gt).le
        have h_p_le : pb * min 1 Rb ≤ q * P.θL * min 1 Rb := mul_le_mul_of_nonneg_right hpL hm0'
        have h_w_le : w * min 1 Rb ≤ w * Rb := mul_le_mul_of_nonneg_left (min_le_right 1 Rb) hw_pos.le
        rcases le_or_gt (q * P.θL - w) 0 with hL0 | hL0
        · have := mul_nonpos_of_nonpos_of_nonneg hL0 hm0'
          have := mul_pos (sub_pos.mpr hwH) hαb0
          linarith
        · have hm_le : min 1 Rb ≤ min (I + Qbar) 1 := by
            rw [min_comm 1 Rb]; exact min_le_min_right 1 hRb_le_S
          have := mul_le_mul_of_nonneg_left hm_le hL0.le
          linarith
      · rcases le_or_gt pb (q * P.θH) with hpH | hpH
        · rw [if_neg (not_le_of_gt hpL), if_pos hpH, zero_add, min_eq_left hRb_gt.le]
          have := mul_le_mul_of_nonneg_right hpH hαb0.le
          have := mul_lt_mul_of_pos_left hRb_gt hw_pos
          linarith
        · rw [if_neg (not_le_of_gt hpL), if_neg (not_le_of_gt hpH), add_zero,
            min_eq_left (lt_trans hαb0 hRb_gt).le, mul_zero]
          have := mul_pos hw_pos (lt_trans hαb0 hRb_gt)
          have := mul_pos (sub_pos.mpr hwH) hαb0
          linarith
    linarith
  · have hsv_I := (sv_bounds_strict_w_p2 P hStand' hQ0 σ hpost hq_pos hc_lt_w hwH hI0).2.2.1 hBrH
    have hslope : P.ρ * w - P.cost q < 0 := by
      have := (lt_div_iff₀' hρ0).mp hw_lt_cρ; linarith
    let B := max P.αb (P.αg - Qbar)
    have hB0 : 0 ≤ B := le_trans hαb0.le (le_max_left _ _)
    rcases lt_or_ge B I with hBI | hIB
    · have hsv_B := (sv_bounds_strict_w_p2 P hStand' hQ0 σ hpost hq_pos hc_lt_w hwH hB0).1
      have hopt := hI_opt B hB0
      have hBQ : P.αg ≤ B + Qbar := by have := le_max_right P.αb (P.αg - Qbar); dsimp [B]; linarith
      have hB_ag : B ≤ P.αg := max_le hαb_αg.le (by linarith)
      unfold fh_p2 at hsv_I hsv_B
      rw [min_eq_left (by linarith : P.αg ≤ I + Qbar), min_eq_left (by linarith : P.αb ≤ I + Qbar),
        max_eq_left hI_gt.le] at hsv_I
      rw [min_eq_left hBQ, max_eq_right hB_ag, min_eq_left (by linarith : P.αb ≤ B + Qbar),
        max_eq_left (le_max_left _ _)] at hsv_B
      have hg_le : w * P.αg - P.cost q * max I P.αg ≤ w * P.αg - P.cost q * P.αg := by
        have := mul_le_mul_of_nonneg_left (le_max_right I P.αg) hc_pos.le; linarith
      have hb_lt : w * P.αb - P.cost q * I < w * P.αb - P.cost q * B := by
        have := mul_lt_mul_of_pos_left hBI hc_pos; linarith
      have := mul_le_mul_of_nonneg_left hg_le hρ0.le
      have := mul_lt_mul_of_pos_left hb_lt h1ρ
      linarith
    · have hsv_ab := (sv_bounds_strict_w_p2 P hStand' hQ0 σ hpost hq_pos hc_lt_w hwH hαb0.le).1
      have hopt := hI_opt P.αb hαb0.le
      have hIQ : I + Qbar ≤ P.αg := by
        have hB_eq : B = P.αg - Qbar := max_eq_right (by
          by_contra hc'
          have : B = P.αb := max_eq_left (le_of_not_ge hc')
          linarith)
        linarith
      unfold fh_p2 at hsv_I hsv_ab
      rw [min_eq_right hIQ, max_eq_right (by linarith : I ≤ I + Qbar),
        min_eq_left (by linarith : P.αb ≤ I + Qbar), max_eq_left hI_gt.le] at hsv_I
      rw [min_eq_right (by linarith : P.αb + Qbar ≤ P.αg),
        max_eq_right (by linarith : P.αb ≤ P.αb + Qbar),
        min_eq_left (by linarith : P.αb ≤ P.αb + Qbar), max_self] at hsv_ab
      have hid : (P.ρ * (w * (I + Qbar) - P.cost q * (I + Qbar)) +
            (1 - P.ρ) * (w * P.αb - P.cost q * I)) -
          (P.ρ * (w * (P.αb + Qbar) - P.cost q * (P.αb + Qbar)) +
            (1 - P.ρ) * (w * P.αb - P.cost q * P.αb)) =
          (P.ρ * w - P.cost q) * (I - P.αb) := by ring
      have hneg : (P.ρ * w - P.cost q) * (I - P.αb) < 0 :=
        mul_neg_of_neg_of_pos hslope (sub_pos.mpr hI_gt)
      linarith

private lemma tie_props_p2 (P : Params) (hStand : P.Standing) {Qbar : ℝ} (hQ0 : 0 ≤ Qbar)
    (σ : Profile) (hpost : IsPostInventorySPE P Qbar σ)
    {q w : ℝ} (hq_pos : 0 < q) (hwH : w < q * P.θH) (hS_pos : 0 < σ.inv q w + Qbar)
    (htie : (q * P.θH - w) * min P.αb (σ.inv q w + Qbar) =
      (q * P.θL - w) * min (σ.inv q w + Qbar) 1) :
    P.αb < σ.inv q w + Qbar ∧ 0 < q * P.θL - w ∧
    (P.cost q < w → 0 ≤ σ.inv q w →
      (∀ I' : ℝ, 0 ≤ I' → σ.supplierValue P q w I' ≤ σ.supplierValue P q w (σ.inv q w)) →
      P.αg ≤ min (σ.inv q w + Qbar) 1) := by
  rcases hStand with ⟨hθL, hθLH, hk, hρ0, hρ1, hαb0, hαb_lt, hαg_gt, hαg1⟩
  have hStand' : P.Standing := ⟨hθL, hθLH, hk, hρ0, hρ1, hαb0, hαb_lt, hαg_gt, hαg1⟩
  have hθH : 0 < P.θH := lt_trans hθL hθLH
  have hαb_αg : P.αb < P.αg := lt_of_mul_lt_mul_right (lt_trans hαb_lt hαg_gt) hθH.le
  let I := σ.inv q w
  let S := I + Qbar
  have hS_gt_ab : P.αb < S := by
    by_contra hc
    have hle : S ≤ P.αb := le_of_not_gt hc
    rw [min_eq_right hle, min_eq_left (le_trans hle (lt_trans hαb_αg hαg1).le)] at htie
    have h1 : q * P.θH - w = q * P.θL - w := mul_right_cancel₀ hS_pos.ne' htie
    have := mul_lt_mul_of_pos_left hθLH hq_pos
    linarith
  have hwL_pos : 0 < q * P.θL - w := by
    rw [min_eq_left hS_gt_ab.le] at htie
    exact pos_of_mul_pos_left
      (by rw [← htie]; exact mul_pos (sub_pos.mpr hwH) hαb0)
      (le_min hS_pos.le zero_le_one)
  refine ⟨hS_gt_ab, hwL_pos, fun hc_lt_w hI0 hI_opt => ?_⟩
  refine le_min ?_ hαg1.le
  by_contra hc
  have hS_lt_ag : S < P.αg := lt_of_not_ge hc
  let J₂ := P.αg - Qbar
  have hJ₂0 : 0 ≤ J₂ := by dsimp [J₂]; linarith
  have hJ₂Q : J₂ + Qbar = P.αg := sub_add_cancel P.αg Qbar
  have hL_J₂ : (q * P.θH - w) * min P.αb (J₂ + Qbar) < (q * P.θL - w) * min (J₂ + Qbar) 1 := by
    rw [hJ₂Q, min_eq_left hαb_αg.le, min_eq_left hαg1.le]
    have htie' : (q * P.θH - w) * P.αb = (q * P.θL - w) * S := by
      rwa [min_eq_left hS_gt_ab.le, min_eq_left (le_trans hS_lt_ag.le hαg1.le)] at htie
    rw [htie']
    exact mul_lt_mul_of_pos_left hS_lt_ag hwL_pos
  have hsv_J₂ := (sv_bounds_strict_w_p2 P hStand' hQ0 σ hpost hq_pos hc_lt_w hwH hJ₂0).2.2.2 hL_J₂
  have hsv_I_ub := (sv_bounds_strict_w_p2 P hStand' hQ0 σ hpost hq_pos hc_lt_w hwH hI0).2.1
  unfold fl_p2 at hsv_J₂ hsv_I_ub
  rw [hJ₂Q, min_self, min_eq_left hαg1.le, max_eq_right (by dsimp [J₂]; linarith : J₂ ≤ P.αg)] at hsv_J₂
  rw [min_eq_right hS_lt_ag.le, min_eq_left (le_trans hS_lt_ag.le hαg1.le),
    max_eq_right (by dsimp [S]; linarith : I ≤ S)] at hsv_I_ub
  have hlt_ag : (w - P.cost q) * S < (w - P.cost q) * P.αg :=
    mul_lt_mul_of_pos_left hS_lt_ag (sub_pos.mpr hc_lt_w)
  have hopt := hI_opt J₂ hJ₂0
  linarith

private lemma tie_step_p2 (P : Params) (hStand : P.Standing)
    {Q₁ Q₂ : ℝ} (hQ₁0 : 0 ≤ Q₁) (hQlt : Q₁ < Q₂)
    (σ₁ : Profile) (hpost₁ : IsPostInventorySPE P Q₁ σ₁)
    (σ₂ : Profile) (hSPE₂ : IsSPE P Q₂ σ₂)
    {q w : ℝ} (hq_pos : 0 < q) (hcw : P.cost q ≤ w) (hw_lt_c1ρ : w < P.cost q / (1 - P.ρ))
    (hwH : w < q * P.θH) (hI₁0 : 0 ≤ σ₁.inv q w)
    (hI₁_opt : ∀ I' : ℝ, 0 ≤ I' → σ₁.supplierValue P q w I' ≤ σ₁.supplierValue P q w (σ₁.inv q w))
    (hsv₁_nn : 0 ≤ σ₁.supplierValue P q w (σ₁.inv q w))
    (hS₀_gt : P.αg + Q₂ < min (σ₁.inv q w + Q₁) 1)
    (htie : (q * P.θH - w) * P.αb = (q * P.θL - w) * min (σ₁.inv q w + Q₁) 1) :
    P.ρ * ((q * P.θH - w) * P.αg) + (1 - P.ρ) * ((q * P.θL - w) * min (σ₁.inv q w + Q₁) 1) ≤
      σ₂.retailerValue P σ₂.q σ₂.w := by
  rcases hSPE₂ with ⟨hpost₂, hinv₂, _, _, hropt₂⟩
  rcases hStand with ⟨hθL, hθLH, hk, hρ0, hρ1, hαb0, hαb_lt, hαg_gt, hαg1⟩
  have hStand' : P.Standing := ⟨hθL, hθLH, hk, hρ0, hρ1, hαb0, hαb_lt, hαg_gt, hαg1⟩
  have hθH : 0 < P.θH := lt_trans hθL hθLH
  have hαg0 : 0 < P.αg := pos_of_mul_pos_left (lt_trans hθL hαg_gt) hθH.le
  have hαb_αg : P.αb < P.αg := lt_of_mul_lt_mul_right (lt_trans hαb_lt hαg_gt) hθH.le
  have h1ρ : 0 < 1 - P.ρ := sub_pos.mpr hρ1
  have hQ₂0 : 0 ≤ Q₂ := le_trans hQ₁0 hQlt.le
  let c := P.cost q
  have hc_pos : 0 < c := mul_pos hk (pow_pos hq_pos 2)
  let I₁ := σ₁.inv q w
  let S₀ := min (I₁ + Q₁) 1
  have hS₀_hi : S₀ ≤ 1 := min_le_right _ _
  have hS₀_IQ₁ : S₀ ≤ I₁ + Q₁ := min_le_left _ _
  have hI₁_gt_ag : P.αg < I₁ := by linarith
  have hc_lt_w : c < w := by
    rcases eq_or_lt_of_le hcw with hweq | hlt
    · exfalso
      exact not_le_of_gt hI₁_gt_ag
        (w_eq_cost_inv_le_ag_p2 P hStand' hQ₁0 σ₁ hpost₁ hq_pos hweq.symm hwH hI₁0 hsv₁_nn)
    · exact hlt
  have hwL0 : 0 < q * P.θL - w :=
    pos_of_mul_pos_left (by rw [← htie]; exact mul_pos (sub_pos.mpr hwH) hαb0)
      (by linarith : 0 ≤ S₀)
  have hc1ρ : (1 - P.ρ) * w < c := (lt_div_iff₀' h1ρ).mp hw_lt_c1ρ
  let V₁ := P.ρ * (w * P.αg - c * (S₀ - Q₁)) + (1 - P.ρ) * (w - c) * S₀
  have hsv₁_le_V₁ : σ₁.supplierValue P q w I₁ ≤ V₁ := by
    have hub := (sv_bounds_strict_w_p2 P hStand' hQ₁0 σ₁ hpost₁ hq_pos hc_lt_w hwH hI₁0).2.1
    unfold fl_p2 at hub
    rw [min_eq_left (by linarith : P.αg ≤ I₁ + Q₁), max_eq_left hI₁_gt_ag.le] at hub
    have h1 : c * (S₀ - Q₁) ≤ c * I₁ := mul_le_mul_of_nonneg_left (by linarith) hc_pos.le
    have h2 : c * S₀ ≤ c * max I₁ S₀ := mul_le_mul_of_nonneg_left (le_max_right _ _) hc_pos.le
    have := mul_le_mul_of_nonneg_left (by dsimp [c] at *; linarith :
      w * P.αg - P.cost q * I₁ ≤ w * P.αg - c * (S₀ - Q₁)) hρ0.le
    have := mul_le_mul_of_nonneg_left (by dsimp [c, S₀] at *; linarith :
      w * S₀ - P.cost q * max I₁ S₀ ≤ (w - c) * S₀) h1ρ.le
    dsimp [V₁]; linarith
  let B₁ := max P.αb (P.αg - Q₁)
  let B₂ := max P.αb (P.αg - Q₂)
  have hB₁0 : 0 ≤ B₁ := le_trans hαb0.le (le_max_left _ _)
  have hB₂0 : 0 ≤ B₂ := le_trans hαb0.le (le_max_left _ _)
  have hfh_ab₁ : fh_p2 P Q₁ q w P.αb ≤ V₁ :=
    le_trans (sv_bounds_strict_w_p2 P hStand' hQ₁0 σ₁ hpost₁ hq_pos hc_lt_w hwH hαb0.le).1
      (le_trans (hI₁_opt P.αb hαb0.le) hsv₁_le_V₁)
  have hfh_B₁ : fh_p2 P Q₁ q w B₁ ≤ V₁ :=
    le_trans (sv_bounds_strict_w_p2 P hStand' hQ₁0 σ₁ hpost₁ hq_pos hc_lt_w hwH hB₁0).1
      (le_trans (hI₁_opt B₁ hB₁0) hsv₁_le_V₁)
  have hB₂_diff : fh_p2 P Q₂ q w B₂ - fh_p2 P Q₂ q w P.αb = (P.ρ * w - c) * (B₂ - P.αb) := by
    rcases le_or_gt (P.αg - Q₂) P.αb with h1 | h1
    · have hB₂_eq : B₂ = P.αb := max_eq_left h1
      rw [hB₂_eq]; ring
    · have hB₂_eq : B₂ = P.αg - Q₂ := max_eq_right h1.le
      rw [hB₂_eq]; unfold fh_p2; dsimp [c]
      rw [sub_add_cancel, min_self, max_eq_right (by linarith : P.αg - Q₂ ≤ P.αg),
        min_eq_left hαb_αg.le, max_eq_left h1.le,
        min_eq_right (by linarith : P.αb + Q₂ ≤ P.αg),
        max_eq_right (by linarith : P.αb ≤ P.αb + Q₂),
        min_eq_left (by linarith : P.αb ≤ P.αb + Q₂), max_self]
      ring
  let H₂ := max (fh_p2 P Q₂ q w P.αb) (fh_p2 P Q₂ q w B₂)
  let V_tgt := P.ρ * (w * P.αg - c * (S₀ - Q₂)) + (1 - P.ρ) * (w - c) * S₀
  have hV_diff : V_tgt = V₁ + P.ρ * c * (Q₂ - Q₁) := by dsimp [V_tgt, V₁]; ring
  have hH₂_lt : H₂ < V_tgt := by
    have hB₂_ab : 0 ≤ B₂ - P.αb := sub_nonneg.mpr (le_max_left _ _)
    rcases lt_or_ge (P.ρ * w) c with hρw | hρw
    · have hB₂_le : fh_p2 P Q₂ q w B₂ ≤ fh_p2 P Q₂ q w P.αb := by
        have := mul_nonpos_of_nonpos_of_nonneg (by linarith : P.ρ * w - c ≤ 0) hB₂_ab
        linarith
      have hH₂_eq : H₂ = fh_p2 P Q₂ q w P.αb := max_eq_left hB₂_le
      have hab_step : fh_p2 P Q₂ q w P.αb - fh_p2 P Q₁ q w P.αb ≤ P.ρ * (w - c) * (Q₂ - Q₁) := by
        unfold fh_p2; dsimp [c]
        rw [max_eq_right (le_min hαb_αg.le (by linarith : P.αb ≤ P.αb + Q₂)),
          min_eq_left (by linarith : P.αb ≤ P.αb + Q₂), max_self,
          max_eq_right (le_min hαb_αg.le (by linarith : P.αb ≤ P.αb + Q₁)),
          min_eq_left (by linarith : P.αb ≤ P.αb + Q₁), max_self]
        have hm : min P.αg (P.αb + Q₂) - min P.αg (P.αb + Q₁) ≤ Q₂ - Q₁ := by
          rcases min_cases P.αg (P.αb + Q₁) with ⟨h1, h2⟩ | ⟨h1, h2⟩
          · have := min_le_left P.αg (P.αb + Q₂); linarith
          · have := min_le_right P.αg (P.αb + Q₂); linarith
        have := mul_le_mul_of_nonneg_left hm (mul_pos hρ0 (sub_pos.mpr hc_lt_w)).le
        dsimp [c] at this
        linarith
      have hwc_lt : w - c < c := by linarith
      have hstrict := mul_lt_mul_of_pos_right
        (mul_lt_mul_of_pos_left hwc_lt hρ0) (sub_pos.mpr hQlt)
      linarith
    · have hab_le : fh_p2 P Q₂ q w P.αb ≤ fh_p2 P Q₂ q w B₂ := by
        have := mul_nonneg (by linarith : 0 ≤ P.ρ * w - c) hB₂_ab
        linarith
      have hH₂_eq : H₂ = fh_p2 P Q₂ q w B₂ := max_eq_right hab_le
      have hB_step : fh_p2 P Q₂ q w B₂ - fh_p2 P Q₁ q w B₁ ≤ (1 - P.ρ) * c * (Q₂ - Q₁) := by
        unfold fh_p2; dsimp [c]
        have hB₁Q : P.αg ≤ B₁ + Q₁ := by have := le_max_right P.αb (P.αg - Q₁); dsimp [B₁]; linarith
        have hB₂Q : P.αg ≤ B₂ + Q₂ := by have := le_max_right P.αb (P.αg - Q₂); dsimp [B₂]; linarith
        rw [min_eq_left hB₂Q, max_eq_right (max_le hαb_αg.le (by linarith)),
          min_eq_left (le_trans (le_max_left _ _) (by linarith : B₂ ≤ B₂ + Q₂)),
          max_eq_left (le_max_left _ _),
          min_eq_left hB₁Q, max_eq_right (max_le hαb_αg.le (by linarith)),
          min_eq_left (le_trans (le_max_left _ _) (by linarith : B₁ ≤ B₁ + Q₁)),
          max_eq_left (le_max_left _ _)]
        have hBd : B₁ - B₂ ≤ Q₂ - Q₁ := by
          dsimp [B₁, B₂]
          rcases max_cases P.αb (P.αg - Q₁) with ⟨h1, _⟩ | ⟨h1, _⟩
          · have := le_max_left P.αb (P.αg - Q₂); linarith
          · have := le_max_right P.αb (P.αg - Q₂); linarith
        have := mul_le_mul_of_nonneg_left hBd (mul_pos h1ρ hc_pos).le
        linarith
      have hρ_cmp : 1 - P.ρ < P.ρ :=
        lt_of_mul_lt_mul_right (lt_of_lt_of_le hc1ρ hρw) (lt_trans hc_pos hc_lt_w).le
      have hstrict := mul_lt_mul_of_pos_right
        (mul_lt_mul_of_pos_right hρ_cmp hc_pos) (sub_pos.mpr hQlt)
      linarith
  let g := V_tgt - H₂
  have hg_pos : 0 < g := sub_pos.mpr hH₂_lt
  let δS := (q * P.θL - w) * (S₀ - (P.αg + Q₂))
  have hδS_pos : 0 < δS := mul_pos hwL0 (sub_pos.mpr hS₀_gt)
  let ε := min ((w - c) / 2) (min (g / 2) (δS / 2))
  have hε_pos : 0 < ε :=
    lt_min (half_pos (sub_pos.mpr hc_lt_w)) (lt_min (half_pos hg_pos) (half_pos hδS_pos))
  have hε1 : ε ≤ (w - c) / 2 := min_le_left _ _
  have hε2 : ε ≤ g / 2 := le_trans (min_le_right _ _) (min_le_left _ _)
  have hε3 : ε ≤ δS / 2 := le_trans (min_le_right _ _) (min_le_right _ _)
  let w' := w - ε
  have hw'_gt_c : P.cost q < w' := by dsimp [w', c] at *; linarith
  have hw'0 : 0 ≤ w' := (lt_trans hc_pos hw'_gt_c).le
  have hw'_lt_w : w' < w := by dsimp [w']; linarith
  have hw'_lt_L : w' < q * P.θL := lt_trans hw'_lt_w (sub_pos.mp hwL0)
  have hw'_lt_H : w' < q * P.θH := lt_trans hw'_lt_w hwH
  have hw'L0 : 0 < q * P.θL - w' := sub_pos.mpr hw'_lt_L
  let S₀' := (q * P.θH - w') * P.αb / (q * P.θL - w')
  have hS₀'_gt : P.αg + Q₂ < S₀' := by
    dsimp [S₀']
    rw [lt_div_iff₀ hw'L0]
    have h1 : ε * (P.αg + Q₂ - P.αb) ≤ ε :=
      mul_le_of_le_one_right hε_pos.le (by linarith)
    dsimp [w', δS] at htie hε3 ⊢
    linarith
  have hS₀'_lt : S₀' < S₀ := by
    dsimp [S₀']
    rw [div_lt_iff₀ hw'L0]
    have hid : (q * P.θL - (w - ε)) * S₀ - (q * P.θH - (w - ε)) * P.αb =
        (q * P.θL - w) * S₀ - (q * P.θH - w) * P.αb + ε * (S₀ - P.αb) := by ring
    have hpos : 0 < ε * (S₀ - P.αb) := mul_pos hε_pos (by linarith)
    dsimp [w']
    linarith
  let J_star := S₀ - Q₂
  have hJs_ag : P.αg < J_star := by dsimp [J_star]; linarith
  have hJs0 : 0 ≤ J_star := (lt_trans hαg0 hJs_ag).le
  have hJsQ : J_star + Q₂ = S₀ := sub_add_cancel S₀ Q₂
  have hL_Js : (q * P.θH - w') * min P.αb (J_star + Q₂) <
      (q * P.θL - w') * min (J_star + Q₂) 1 := by
    rw [hJsQ, min_eq_left (by linarith : P.αb ≤ S₀), min_eq_left hS₀_hi]
    have h1 : (q * P.θH - w') * P.αb = (q * P.θL - w') * S₀' := by
      dsimp [S₀']; rw [mul_div_cancel₀ _ hw'L0.ne']
    rw [h1]; exact mul_lt_mul_of_pos_left hS₀'_lt hw'L0
  have hsv₂_Js := (sv_bounds_strict_w_p2 P hStand' hQ₂0 σ₂ hpost₂ hq_pos hw'_gt_c hw'_lt_H hJs0).2.2.2 hL_Js
  unfold fl_p2 at hsv₂_Js
  rw [hJsQ, min_eq_left (by linarith : P.αg ≤ S₀), max_eq_left hJs_ag.le,
    min_eq_left hS₀_hi, max_eq_right (by dsimp [J_star]; linarith : J_star ≤ S₀)] at hsv₂_Js
  have hfh_mono_w : ∀ J : ℝ, 0 ≤ J → fh_p2 P Q₂ q w' J ≤ fh_p2 P Q₂ q w J := by
    intro J hJ0
    unfold fh_p2
    have h1 : w' * min P.αg (J + Q₂) ≤ w * min P.αg (J + Q₂) :=
      mul_le_mul_of_nonneg_right hw'_lt_w.le (le_min hαg0.le (add_nonneg hJ0 hQ₂0))
    have h2 : w' * min P.αb (J + Q₂) ≤ w * min P.αb (J + Q₂) :=
      mul_le_mul_of_nonneg_right hw'_lt_w.le (le_min hαb0.le (add_nonneg hJ0 hQ₂0))
    have := mul_le_mul_of_nonneg_left h1 hρ0.le
    have := mul_le_mul_of_nonneg_left h2 h1ρ.le
    linarith
  have hH₂_w'_lt : max (fh_p2 P Q₂ q w' P.αb) (fh_p2 P Q₂ q w' B₂) <
      σ₂.supplierValue P q w' J_star := by
    have hle_H₂ : max (fh_p2 P Q₂ q w' P.αb) (fh_p2 P Q₂ q w' B₂) ≤ H₂ :=
      max_le_max (hfh_mono_w P.αb hαb0.le) (hfh_mono_w B₂ hB₂0)
    have hwt : P.ρ * P.αg + (1 - P.ρ) * S₀ ≤ 1 := by
      have := mul_le_mul_of_nonneg_left hαg1.le hρ0.le
      have := mul_le_mul_of_nonneg_left hS₀_hi h1ρ.le
      linarith
    have hdrop : (P.ρ * P.αg + (1 - P.ρ) * S₀) * ε ≤ ε :=
      mul_le_of_le_one_left hε_pos.le hwt
    rw [hsv₂_Js]
    dsimp [J_star, w', V_tgt, g, c] at *
    linarith
  obtain ⟨hI₂0, hI₂_opt⟩ := hinv₂ q w' hq_pos.le hw'0
  let I₂ := σ₂.inv q w'
  have hI₂_ge : S₀' - Q₂ ≤ I₂ := by
    by_contra hc
    have hlt : I₂ + Q₂ < S₀' := by linarith
    have hS₂_pos : 0 < I₂ + Q₂ := by linarith
    have hH_I₂ : (q * P.θL - w') * min (I₂ + Q₂) 1 <
        (q * P.θH - w') * min P.αb (I₂ + Q₂) := by
      rw [min_eq_left (le_trans hlt.le (le_trans hS₀'_lt.le hS₀_hi))]
      rcases le_or_gt (I₂ + Q₂) P.αb with hab | hab
      · rw [min_eq_right hab]
        exact mul_lt_mul_of_pos_right (by have := mul_lt_mul_of_pos_left hθLH hq_pos; linarith) hS₂_pos
      · rw [min_eq_left hab.le]
        have h1 : (q * P.θH - w') * P.αb = (q * P.θL - w') * S₀' := by
          dsimp [S₀']; rw [mul_div_cancel₀ _ hw'L0.ne']
        rw [h1]; exact mul_lt_mul_of_pos_left hlt hw'L0
    have hsv₂_I₂ := (sv_bounds_strict_w_p2 P hStand' hQ₂0 σ₂ hpost₂ hq_pos hw'_gt_c hw'_lt_H hI₂0).2.2.1 hH_I₂
    have hmax_I₂ := fh_max_p2 P hStand' hQ₂0 hq_pos hw'_gt_c hI₂0
    have hopt_Js := hI₂_opt J_star hJs0
    dsimp [I₂, B₂] at *
    linarith
  have hlb₂ := rv_lb_strict_w_p2 P hStand' hQ₂0 σ₂ hpost₂ hq_pos hw'_gt_c hw'_lt_H hI₂0
  have hg₂ : min P.αg (I₂ + Q₂) = P.αg := min_eq_left (by linarith)
  have hb₂ : min P.αb (I₂ + Q₂) = P.αb := min_eq_left (by linarith)
  rw [hg₂, hb₂] at hlb₂
  have hb_pay : (q * P.θH - w') * P.αb ≤
      max ((q * P.θH - w') * P.αb) ((q * P.θL - w') * min (I₂ + Q₂) 1) := le_max_left _ _
  have := mul_le_mul_of_nonneg_left hb_pay h1ρ.le
  have hopt₂ := hropt₂ q w' hq_pos.le hw'0
  have heps_gain : 0 < (P.ρ * P.αg + (1 - P.ρ) * P.αb) * ε :=
    mul_pos (add_pos (mul_pos hρ0 hαg0) (mul_pos h1ρ hαb0)) hε_pos
  have hid_tie :
      P.ρ * ((q * P.θH - w') * P.αg) + (1 - P.ρ) * ((q * P.θH - w') * P.αb) =
        P.ρ * ((q * P.θH - w) * P.αg) + (1 - P.ρ) * ((q * P.θH - w) * P.αb) +
          (P.ρ * P.αg + (1 - P.ρ) * P.αb) * ε := by
    dsimp [w']; ring
  rw [htie] at hid_tie
  linarith

private lemma clause1_p2 (P : Params) (hStand : P.Standing) (hFocus : P.Focus)
    (Q₁ Q₂ : ℝ) (e₁ e₂ : Outcome) (hQ₁0 : 0 ≤ Q₁) (hQlt : Q₁ < Q₂)
    (he₁ : IsEquilibrium P Q₁ e₁) (he₂ : IsEquilibrium P Q₂ e₂) :
    e₁.πR ≤ e₂.πR := by
  rcases he₁ with ⟨σ₁, hSPE₁, rfl⟩
  rcases he₂ with ⟨σ₂, hSPE₂, rfl⟩
  change σ₁.retailerValue P σ₁.q σ₁.w ≤ σ₂.retailerValue P σ₂.q σ₂.w
  have hQ₂0 : 0 ≤ Q₂ := le_trans hQ₁0 hQlt.le
  have hvos₂ := lb_vos_p2 P hStand hFocus hQ₂0 hSPE₂
  have hvoo₂ := lb_voo_p2 P hStand hFocus hQ₂0 hSPE₂
  have hvhos₂ := lb_vhos_p2 P hStand hQ₂0 hSPE₂
  have hvos₀_le : P.V_OS 0 ≤ P.V_OS Q₂ := vos_mono_p2 P hStand hFocus (le_refl 0) hQ₂0
  have hvos₁_le : P.V_OS Q₁ ≤ P.V_OS Q₂ := vos_mono_p2 P hStand hFocus hQ₁0 hQlt.le
  obtain ⟨hθH, hαg0, hαb_αg, _, h1ρ, hD1, _, _, _⟩ := standing_focus_p2 P hStand hFocus
  rcases hStand with ⟨hθL, hθLH, hk, hρ0, hρ1, hαb0, hαb_lt, hαg_gt, hαg1⟩
  have hStand' : P.Standing := ⟨hθL, hθLH, hk, hρ0, hρ1, hαb0, hαb_lt, hαg_gt, hαg1⟩
  have hvos₀_pos : 0 < P.V_OS 0 :=
    lt_trans (div_pos (mul_pos (mul_pos (add_pos (mul_pos hρ0 hαg0) (mul_pos h1ρ hαb0)) hρ0)
      (pow_pos hθH 2)) (by linarith)) (ho_over_lt_vos0_p2 P hStand' hFocus)
  rcases hSPE₁ with ⟨hpost₁, hinv₁, hq0, hw0, _⟩
  let q := σ₁.q
  let w := σ₁.w
  obtain ⟨hI₁0, hI₁_opt⟩ := hinv₁ q w hq0 hw0
  have hsv₁_nn := le_trans (sv0_nonneg_p2 P hStand' hQ₁0 σ₁ hpost₁ hq0 hw0) (hI₁_opt 0 (le_refl 0))
  by_cases hact : P.cost q ≤ w ∧ 0 < q ∧ w < q * P.θH
  · rcases hact with ⟨hcw, hq_pos, hwH⟩
    have hwH0 : 0 < q * P.θH - w := sub_pos.mpr hwH
    obtain ⟨hub0, hub_pos⟩ := active_rv_ub_p2 P hStand' hQ₁0 σ₁ hpost₁ hq_pos hw0 hwH hI₁0
    let S₁ := σ₁.inv q w + Q₁
    rcases eq_or_lt_of_le (add_nonneg hI₁0 hQ₁0) with hS₁z | hS₁_pos
    · rw [hub0 hS₁z.symm]; linarith
    · have hub := hub_pos hS₁_pos
      rcases lt_trichotomy ((q * P.θL - w) * min S₁ 1) ((q * P.θH - w) * min P.αb S₁) with
        hBrH | htie | hBrL
      · rw [max_eq_left hBrH.le] at hub
        rcases le_or_gt (P.cost q / P.ρ) w with hw_ge_cρ | hw_lt_cρ
        · have hg1 : (q * P.θH - w) * min P.αg S₁ ≤ (q * P.θH - P.cost q / P.ρ) * P.αg :=
            le_trans (mul_le_mul_of_nonneg_left (min_le_left _ _) hwH0.le)
              (mul_le_mul_of_nonneg_right (by linarith) hαg0.le)
          have hb1 : (q * P.θH - w) * min P.αb S₁ ≤ (q * P.θH - P.cost q / P.ρ) * P.αb :=
            le_trans (mul_le_mul_of_nonneg_left (min_le_left _ _) hwH0.le)
              (mul_le_mul_of_nonneg_right (by linarith) hαb0.le)
          have hq_quad : q * P.θH - P.cost q / P.ρ ≤ P.ρ * P.θH ^ 2 / (4 * P.k) := by
            unfold Params.cost
            have hid : P.ρ * P.θH ^ 2 / (4 * P.k) - (q * P.θH - P.k * q ^ 2 / P.ρ) =
                P.k / P.ρ * (q - P.ρ * P.θH / (2 * P.k)) ^ 2 := by
              field_simp [hk.ne', hρ0.ne']; ring
            have hnn : 0 ≤ P.k / P.ρ * (q - P.ρ * P.θH / (2 * P.k)) ^ 2 :=
              mul_nonneg (div_nonneg hk.le hρ0.le) (sq_nonneg _)
            linarith
          have hA : 0 < P.ρ * P.αg + (1 - P.ρ) * P.αb :=
            add_pos (mul_pos hρ0 hαg0) (mul_pos h1ρ hαb0)
          have h1 := mul_le_mul_of_nonneg_left hg1 hρ0.le
          have h2 := mul_le_mul_of_nonneg_left hb1 h1ρ.le
          have h3 := mul_le_mul_of_nonneg_left hq_quad hA.le
          have h3' : (P.ρ * P.αg + (1 - P.ρ) * P.αb) * (q * P.θH - P.cost q / P.ρ) ≤
              (P.ρ * P.αg + (1 - P.ρ) * P.αb) * P.ρ * P.θH ^ 2 / (4 * P.k) :=
            le_trans h3 (by ring_nf; exact le_refl _)
          have hid_sum : P.ρ * ((q * P.θH - P.cost q / P.ρ) * P.αg) +
              (1 - P.ρ) * ((q * P.θH - P.cost q / P.ρ) * P.αb) =
              (P.ρ * P.αg + (1 - P.ρ) * P.αb) * (q * P.θH - P.cost q / P.ρ) := by ring
          have hho := ho_over_lt_vos0_p2 P hStand' hFocus
          linarith
        · have hI_ab := inv_le_ab_strictH_p2 P hStand' hQ₁0 σ₁ hpost₁ hq_pos hcw hw_lt_cρ
            hwH hI₁0 hI₁_opt hsv₁_nn hBrH
          have hg1 : min P.αg S₁ ≤ min P.αg (P.αb + Q₂) :=
            min_le_min_left P.αg (by dsimp [S₁]; linarith)
          have hb1 : min P.αb S₁ ≤ P.αb := min_le_left _ _
          have hq_quad : q * P.θH - w ≤ P.θH ^ 2 / (4 * P.k) := by
            unfold Params.cost at hcw
            have hid : P.θH ^ 2 / (4 * P.k) - (q * P.θH - P.k * q ^ 2) =
                P.k * (q - P.θH / (2 * P.k)) ^ 2 := by field_simp [hk.ne']; ring
            have hnn : 0 ≤ P.k * (q - P.θH / (2 * P.k)) ^ 2 := mul_nonneg hk.le (sq_nonneg _)
            linarith
          have hA : 0 < P.ρ * min P.αg (P.αb + Q₂) + (1 - P.ρ) * P.αb :=
            add_pos (mul_pos hρ0 (lt_min hαg0 (by linarith))) (mul_pos h1ρ hαb0)
          have h1 := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hg1 hwH0.le) hρ0.le
          have h2 := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hb1 hwH0.le) h1ρ.le
          have h3 := mul_le_mul_of_nonneg_left hq_quad hA.le
          rw [← mul_div_assoc] at h3
          have hid_sum : P.ρ * ((q * P.θH - w) * min P.αg (P.αb + Q₂)) +
              (1 - P.ρ) * ((q * P.θH - w) * P.αb) =
              (P.ρ * min P.αg (P.αb + Q₂) + (1 - P.ρ) * P.αb) * (q * P.θH - w) := by ring
          linarith
      · obtain ⟨hS₁_ab, hwL0, _⟩ := tie_props_p2 P hStand' hQ₁0 σ₁ hpost₁ hq_pos hwH hS₁_pos htie.symm
        rw [max_eq_left htie.le, ← htie] at hub
        have hg1 : (q * P.θH - w) * min P.αg S₁ ≤ (q * P.θH - w) * P.αg :=
          mul_le_mul_of_nonneg_left (min_le_left _ _) hwH0.le
        have hub_S₀ : σ₁.retailerValue P q w ≤
            P.ρ * ((q * P.θH - w) * P.αg) + (1 - P.ρ) * ((q * P.θL - w) * min S₁ 1) := by
          have := mul_le_mul_of_nonneg_left hg1 hρ0.le; linarith
        rcases le_or_gt (min S₁ 1) (P.supplyS Q₂) with hS₀_le | hS₀_gt
        · obtain ⟨hDS₂, _, _, _, _⟩ :=
            y_props_p2 P (S := P.supplyS Q₂) hStand' hFocus (le_min (by linarith) hαg1.le) (min_le_right _ _)
          have hquad := ub_quad_os_p2 P (S := P.supplyS Q₂) (q := q) (w := w) hk hDS₂
          have hvos₂_def : (P.ρ * P.αg + (1 - P.ρ) * P.supplyS Q₂) * P.Y (P.supplyS Q₂) ^ 2 / (4 * P.k) =
              P.V_OS Q₂ := rfl
          rw [hvos₂_def] at hquad
          have hb1 : (q * P.θL - w) * min S₁ 1 ≤ (q * P.θL - w) * P.supplyS Q₂ :=
            mul_le_mul_of_nonneg_left hS₀_le hwL0.le
          have hsq : 0 ≤ (P.ρ * P.αg + (1 - P.ρ) * P.supplyS Q₂) * P.k *
              (q - P.Y (P.supplyS Q₂) / (2 * P.k)) ^ 2 :=
            mul_nonneg (mul_nonneg hDS₂.le hk.le) (sq_nonneg _)
          have hwc : 0 ≤ (P.ρ * P.αg + (1 - P.ρ) * P.supplyS Q₂) * (w - P.cost q) :=
            mul_nonneg hDS₂.le (sub_nonneg.mpr hcw)
          have := mul_le_mul_of_nonneg_left hb1 h1ρ.le
          linarith
        · rcases le_or_gt (P.cost q / (1 - P.ρ)) w with hw_ge_c1ρ | hw_lt_c1ρ
          · have hb1 : (q * P.θL - w) * min S₁ 1 ≤ q * P.θL - w := by
              have := mul_le_mul_of_nonneg_left (min_le_right S₁ 1) hwL0.le; linarith
            have := mul_le_mul_of_nonneg_left hb1 h1ρ.le
            have hoo := ub_quad_oo_p2 P hk h1ρ hD1 hw_ge_c1ρ
            linarith
          · have hS₂_lt1 : P.αg + Q₂ < min S₁ 1 := by
              unfold Params.supplyS at hS₀_gt
              rcases le_or_gt (P.αg + Q₂) 1 with h1 | h1
              · rwa [min_eq_left h1] at hS₀_gt
              · exfalso; rw [min_eq_right h1.le] at hS₀_gt
                linarith [min_le_right S₁ 1]
            have htie_ab : (q * P.θH - w) * P.αb = (q * P.θL - w) * min S₁ 1 := by
              have h := htie.symm; rwa [min_eq_left hS₁_ab.le] at h
            exact le_trans hub_S₀ (tie_step_p2 P hStand' hQ₁0 hQlt σ₁ hpost₁ σ₂ hSPE₂
              hq_pos hcw hw_lt_c1ρ hwH hI₁0 hI₁_opt hsv₁_nn hS₂_lt1 htie_ab)
      · rw [max_eq_right hBrL.le] at hub
        have hwL0 : 0 < q * P.θL - w :=
          pos_of_mul_pos_left (lt_of_le_of_lt
            (mul_nonneg hwH0.le (le_min hαb0.le hS₁_pos.le)) hBrL) (le_min hS₁_pos.le zero_le_one)
        have hg1 : (q * P.θH - w) * min P.αg S₁ ≤ (q * P.θH - w) * P.αg :=
          mul_le_mul_of_nonneg_left (min_le_left _ _) hwH0.le
        rcases le_or_gt (1 - P.αg) Q₁ with hQ₁hi | hQ₁med
        · have hS₁_le : min S₁ 1 ≤ P.supplyS Q₁ := by
            rw [show P.supplyS Q₁ = 1 from min_eq_right (by linarith)]; exact min_le_right _ _
          obtain ⟨hDS₁, _, _, _, _⟩ :=
            y_props_p2 P (S := P.supplyS Q₁) hStand' hFocus (le_min (by linarith) hαg1.le) (min_le_right _ _)
          have hquad := ub_quad_os_p2 P (S := P.supplyS Q₁) (q := q) (w := w) hk hDS₁
          have hvos₁_def : (P.ρ * P.αg + (1 - P.ρ) * P.supplyS Q₁) * P.Y (P.supplyS Q₁) ^ 2 / (4 * P.k) =
              P.V_OS Q₁ := rfl
          rw [hvos₁_def] at hquad
          have hb1 := mul_le_mul_of_nonneg_left hS₁_le hwL0.le
          have hsq : 0 ≤ (P.ρ * P.αg + (1 - P.ρ) * P.supplyS Q₁) * P.k *
              (q - P.Y (P.supplyS Q₁) / (2 * P.k)) ^ 2 :=
            mul_nonneg (mul_nonneg hDS₁.le hk.le) (sq_nonneg _)
          have hwc : 0 ≤ (P.ρ * P.αg + (1 - P.ρ) * P.supplyS Q₁) * (w - P.cost q) :=
            mul_nonneg hDS₁.le (sub_nonneg.mpr hcw)
          have := mul_le_mul_of_nonneg_left hg1 hρ0.le
          have := mul_le_mul_of_nonneg_left hb1 h1ρ.le
          linarith
        · rcases le_or_gt (P.cost q / (1 - P.ρ)) w with hw_ge_c1ρ | hw_lt_c1ρ
          · have hb1 : (q * P.θL - w) * min S₁ 1 ≤ q * P.θL - w := by
              have := mul_le_mul_of_nonneg_left (min_le_right S₁ 1) hwL0.le; linarith
            have := mul_le_mul_of_nonneg_left hg1 hρ0.le
            have := mul_le_mul_of_nonneg_left hb1 h1ρ.le
            have hoo := ub_quad_oo_p2 P hk h1ρ hD1 hw_ge_c1ρ
            linarith
          · have hI_ag := inv_le_ag_lt_oo_p2 P hStand' hQ₁0 hQ₁med σ₁ hpost₁
              hq_pos hcw hw_lt_c1ρ (sub_pos.mp hwL0) hI₁0 hI₁_opt hsv₁_nn hBrL
            have hS₁_le : min S₁ 1 ≤ P.supplyS Q₁ :=
              min_le_min_right 1 (by dsimp [S₁]; linarith)
            obtain ⟨hDS₁, _, _, _, _⟩ :=
              y_props_p2 P (S := P.supplyS Q₁) hStand' hFocus (le_min (by linarith) hαg1.le) (min_le_right _ _)
            have hquad := ub_quad_os_p2 P (S := P.supplyS Q₁) (q := q) (w := w) hk hDS₁
            have hvos₁_def : (P.ρ * P.αg + (1 - P.ρ) * P.supplyS Q₁) * P.Y (P.supplyS Q₁) ^ 2 / (4 * P.k) =
                P.V_OS Q₁ := rfl
            rw [hvos₁_def] at hquad
            have hb1 := mul_le_mul_of_nonneg_left hS₁_le hwL0.le
            have hsq : 0 ≤ (P.ρ * P.αg + (1 - P.ρ) * P.supplyS Q₁) * P.k *
                (q - P.Y (P.supplyS Q₁) / (2 * P.k)) ^ 2 :=
              mul_nonneg (mul_nonneg hDS₁.le hk.le) (sq_nonneg _)
            have hwc : 0 ≤ (P.ρ * P.αg + (1 - P.ρ) * P.supplyS Q₁) * (w - P.cost q) :=
              mul_nonneg hDS₁.le (sub_nonneg.mpr hcw)
            have := mul_le_mul_of_nonneg_left hg1 hρ0.le
            have := mul_le_mul_of_nonneg_left hb1 h1ρ.le
            linarith
  · have hnp := inactive_rv_nonpos_p2 P hStand' hQ₁0 σ₁ hpost₁ hq0 hw0 hI₁0 hsv₁_nn hact
    linarith

private lemma piS_zero_above_p2 (P : Params) (hStand : P.Standing) (hFocus : P.Focus)
    {gap Qbar : ℝ}
    (hgap : ∀ q w S₀ : ℝ, 0 < q → P.cost q ≤ w → P.αg ≤ S₀ → S₀ ≤ 1 →
      (q * P.θH - w) * P.αb = (q * P.θL - w) * S₀ →
      P.ρ * ((q * P.θH - w) * P.αg) + (1 - P.ρ) * ((q * P.θL - w) * S₀) ≤
        P.V_OS (1 - P.αg) - gap)
    (hQ0 : 0 ≤ Qbar) (hV_gt : max P.V_OO (P.V_OS (1 - P.αg) - gap) < P.V_OS Qbar)
    {e : Outcome} (he : IsEquilibrium P Qbar e) :
    e.πS = 0 := by
  rcases he with ⟨σ, hSPE, rfl⟩
  have hvos := lb_vos_p2 P hStand hFocus hQ0 hSPE
  have hvhos := lb_vhos_p2 P hStand hQ0 hSPE
  have hvos0_le : P.V_OS 0 ≤ P.V_OS Qbar := vos_mono_p2 P hStand hFocus (le_refl 0) hQ0
  obtain ⟨hθH, hαg0, _, _, h1ρ, hD1, _, _, _⟩ := standing_focus_p2 P hStand hFocus
  rcases hStand with ⟨hθL, hθLH, hk, hρ0, hρ1, hαb0, hαb_lt, hαg_gt, hαg1⟩
  have hStand' : P.Standing := ⟨hθL, hθLH, hk, hρ0, hρ1, hαb0, hαb_lt, hαg_gt, hαg1⟩
  have hvos0_pos : 0 < P.V_OS 0 :=
    lt_trans (div_pos (mul_pos (mul_pos (add_pos (mul_pos hρ0 hαg0) (mul_pos h1ρ hαb0)) hρ0)
      (pow_pos hθH 2)) (by linarith)) (ho_over_lt_vos0_p2 P hStand' hFocus)
  rcases hSPE with ⟨hpost, hinv, hq0, hw0, _⟩
  let q := σ.q
  let w := σ.w
  obtain ⟨hI0, hI_opt⟩ := hinv q w hq0 hw0
  have hsv_nn := le_trans (sv0_nonneg_p2 P hStand' hQ0 σ hpost hq0 hw0) (hI_opt 0 (le_refl 0))
  change σ.supplierValue P q w (σ.inv q w) = 0
  rcases le_or_gt w (P.cost q) with hw_le | hc_lt_w
  · exact (w_le_cost_props_p2 P hStand' hQ0 σ hpost hq0 hw0 hI0 hsv_nn hw_le).1
  · exfalso
    have hact : P.cost q ≤ w ∧ 0 < q ∧ w < q * P.θH := by
      by_contra hna
      have := inactive_rv_nonpos_p2 P hStand' hQ0 σ hpost hq0 hw0 hI0 hsv_nn hna
      linarith
    rcases hact with ⟨_, hq_pos, hwH⟩
    have hwH0 : 0 < q * P.θH - w := sub_pos.mpr hwH
    obtain ⟨hub0, hub_pos⟩ := active_rv_ub_p2 P hStand' hQ0 σ hpost hq_pos hw0 hwH hI0
    let S := σ.inv q w + Qbar
    rcases eq_or_lt_of_le (add_nonneg hI0 hQ0) with hSz | hS_pos
    · have := hub0 hSz.symm; linarith
    · have hub := hub_pos hS_pos
      rcases lt_trichotomy ((q * P.θL - w) * min S 1) ((q * P.θH - w) * min P.αb S) with
        hBrH | htie | hBrL
      · rw [max_eq_left hBrH.le] at hub
        rcases le_or_gt (P.cost q / P.ρ) w with hw_ge_cρ | hw_lt_cρ
        · have hg1 : (q * P.θH - w) * min P.αg S ≤ (q * P.θH - P.cost q / P.ρ) * P.αg :=
            le_trans (mul_le_mul_of_nonneg_left (min_le_left _ _) hwH0.le)
              (mul_le_mul_of_nonneg_right (by linarith) hαg0.le)
          have hb1 : (q * P.θH - w) * min P.αb S ≤ (q * P.θH - P.cost q / P.ρ) * P.αb :=
            le_trans (mul_le_mul_of_nonneg_left (min_le_left _ _) hwH0.le)
              (mul_le_mul_of_nonneg_right (by linarith) hαb0.le)
          have hq_quad : q * P.θH - P.cost q / P.ρ ≤ P.ρ * P.θH ^ 2 / (4 * P.k) := by
            unfold Params.cost
            have hid : P.ρ * P.θH ^ 2 / (4 * P.k) - (q * P.θH - P.k * q ^ 2 / P.ρ) =
                P.k / P.ρ * (q - P.ρ * P.θH / (2 * P.k)) ^ 2 := by
              field_simp [hk.ne', hρ0.ne']; ring
            have hnn : 0 ≤ P.k / P.ρ * (q - P.ρ * P.θH / (2 * P.k)) ^ 2 :=
              mul_nonneg (div_nonneg hk.le hρ0.le) (sq_nonneg _)
            linarith
          have hA : 0 < P.ρ * P.αg + (1 - P.ρ) * P.αb :=
            add_pos (mul_pos hρ0 hαg0) (mul_pos h1ρ hαb0)
          have h1 := mul_le_mul_of_nonneg_left hg1 hρ0.le
          have h2 := mul_le_mul_of_nonneg_left hb1 h1ρ.le
          have h3 := mul_le_mul_of_nonneg_left hq_quad hA.le
          have h3' : (P.ρ * P.αg + (1 - P.ρ) * P.αb) * (q * P.θH - P.cost q / P.ρ) ≤
              (P.ρ * P.αg + (1 - P.ρ) * P.αb) * P.ρ * P.θH ^ 2 / (4 * P.k) :=
            le_trans h3 (by ring_nf; exact le_refl _)
          have hid_sum : P.ρ * ((q * P.θH - P.cost q / P.ρ) * P.αg) +
              (1 - P.ρ) * ((q * P.θH - P.cost q / P.ρ) * P.αb) =
              (P.ρ * P.αg + (1 - P.ρ) * P.αb) * (q * P.θH - P.cost q / P.ρ) := by ring
          have hho := ho_over_lt_vos0_p2 P hStand' hFocus
          linarith
        · have hI_ab := inv_le_ab_strictH_p2 P hStand' hQ0 σ hpost hq_pos hc_lt_w.le hw_lt_cρ
            hwH hI0 hI_opt hsv_nn hBrH
          have hg1 : min P.αg S ≤ min P.αg (P.αb + Qbar) :=
            min_le_min_left P.αg (by dsimp [S]; linarith)
          have hb1 : min P.αb S ≤ P.αb := min_le_left _ _
          have hq_strict : q * P.θH - w < P.θH ^ 2 / (4 * P.k) := by
            unfold Params.cost at hc_lt_w
            have hid : P.θH ^ 2 / (4 * P.k) - (q * P.θH - P.k * q ^ 2) =
                P.k * (q - P.θH / (2 * P.k)) ^ 2 := by field_simp [hk.ne']; ring
            have hnn : 0 ≤ P.k * (q - P.θH / (2 * P.k)) ^ 2 := mul_nonneg hk.le (sq_nonneg _)
            linarith
          have hA : 0 < P.ρ * min P.αg (P.αb + Qbar) + (1 - P.ρ) * P.αb :=
            add_pos (mul_pos hρ0 (lt_min hαg0 (by linarith))) (mul_pos h1ρ hαb0)
          have h1 := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hg1 hwH0.le) hρ0.le
          have h2 := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hb1 hwH0.le) h1ρ.le
          have h3 := mul_lt_mul_of_pos_left hq_strict hA
          rw [← mul_div_assoc] at h3
          have hid_sum : P.ρ * ((q * P.θH - w) * min P.αg (P.αb + Qbar)) +
              (1 - P.ρ) * ((q * P.θH - w) * P.αb) =
              (P.ρ * min P.αg (P.αb + Qbar) + (1 - P.ρ) * P.αb) * (q * P.θH - w) := by ring
          linarith
      · obtain ⟨hS_ab, _, hS_ag_fn⟩ := tie_props_p2 P hStand' hQ0 σ hpost hq_pos hwH hS_pos htie.symm
        have hS₀_lo := hS_ag_fn hc_lt_w hI0 hI_opt
        rw [max_eq_left htie.le, ← htie] at hub
        have hg1 := mul_le_mul_of_nonneg_left (min_le_left P.αg S) hwH0.le
        have := mul_le_mul_of_nonneg_left hg1 hρ0.le
        have htie_ab : (q * P.θH - w) * P.αb = (q * P.θL - w) * min S 1 := by
          have h := htie.symm; rwa [min_eq_left hS_ab.le] at h
        have ht_ub := hgap q w (min S 1) hq_pos hc_lt_w.le hS₀_lo (min_le_right _ _) htie_ab
        have := le_max_right P.V_OO (P.V_OS (1 - P.αg) - gap)
        linarith
      · rw [max_eq_right hBrL.le] at hub
        have hwL0 : 0 < q * P.θL - w :=
          pos_of_mul_pos_left (lt_of_le_of_lt
            (mul_nonneg hwH0.le (le_min hαb0.le hS_pos.le)) hBrL) (le_min hS_pos.le zero_le_one)
        have hg1 := mul_le_mul_of_nonneg_left (min_le_left P.αg S) hwH0.le
        rcases le_or_gt (1 - P.αg) Qbar with hQhi | hQmed
        · have hS_le : min S 1 ≤ P.supplyS Qbar := by
            rw [show P.supplyS Qbar = 1 from min_eq_right (by linarith)]; exact min_le_right _ _
          obtain ⟨hDS, _, _, _, _⟩ :=
            y_props_p2 P (S := P.supplyS Qbar) hStand' hFocus (le_min (by linarith) hαg1.le) (min_le_right _ _)
          have hquad := ub_quad_os_p2 P (S := P.supplyS Qbar) (q := q) (w := w) hk hDS
          have hvos_def : (P.ρ * P.αg + (1 - P.ρ) * P.supplyS Qbar) * P.Y (P.supplyS Qbar) ^ 2 / (4 * P.k) =
              P.V_OS Qbar := rfl
          rw [hvos_def] at hquad
          have hb1 := mul_le_mul_of_nonneg_left hS_le hwL0.le
          have hsq : 0 ≤ (P.ρ * P.αg + (1 - P.ρ) * P.supplyS Qbar) * P.k *
              (q - P.Y (P.supplyS Qbar) / (2 * P.k)) ^ 2 :=
            mul_nonneg (mul_nonneg hDS.le hk.le) (sq_nonneg _)
          have hwc : 0 < (P.ρ * P.αg + (1 - P.ρ) * P.supplyS Qbar) * (w - P.cost q) :=
            mul_pos hDS (sub_pos.mpr hc_lt_w)
          have := mul_le_mul_of_nonneg_left hg1 hρ0.le
          have := mul_le_mul_of_nonneg_left hb1 h1ρ.le
          linarith
        · rcases le_or_gt (P.cost q / (1 - P.ρ)) w with hw_ge_c1ρ | hw_lt_c1ρ
          · have hb1 : (q * P.θL - w) * min S 1 ≤ q * P.θL - w := by
              have := mul_le_mul_of_nonneg_left (min_le_right S 1) hwL0.le; linarith
            have := mul_le_mul_of_nonneg_left hg1 hρ0.le
            have := mul_le_mul_of_nonneg_left hb1 h1ρ.le
            have hoo := ub_quad_oo_p2 P hk h1ρ hD1 hw_ge_c1ρ
            have := le_max_left P.V_OO (P.V_OS (1 - P.αg) - gap)
            linarith
          · have hI_ag := inv_le_ag_lt_oo_p2 P hStand' hQ0 hQmed σ hpost
              hq_pos hc_lt_w.le hw_lt_c1ρ (sub_pos.mp hwL0) hI0 hI_opt hsv_nn hBrL
            have hS_le : min S 1 ≤ P.supplyS Qbar :=
              min_le_min_right 1 (by dsimp [S]; linarith)
            obtain ⟨hDS, _, _, _, _⟩ :=
              y_props_p2 P (S := P.supplyS Qbar) hStand' hFocus (le_min (by linarith) hαg1.le) (min_le_right _ _)
            have hquad := ub_quad_os_p2 P (S := P.supplyS Qbar) (q := q) (w := w) hk hDS
            have hvos_def : (P.ρ * P.αg + (1 - P.ρ) * P.supplyS Qbar) * P.Y (P.supplyS Qbar) ^ 2 / (4 * P.k) =
                P.V_OS Qbar := rfl
            rw [hvos_def] at hquad
            have hb1 := mul_le_mul_of_nonneg_left hS_le hwL0.le
            have hsq : 0 ≤ (P.ρ * P.αg + (1 - P.ρ) * P.supplyS Qbar) * P.k *
                (q - P.Y (P.supplyS Qbar) / (2 * P.k)) ^ 2 :=
              mul_nonneg (mul_nonneg hDS.le hk.le) (sq_nonneg _)
            have hwc : 0 < (P.ρ * P.αg + (1 - P.ρ) * P.supplyS Qbar) * (w - P.cost q) :=
              mul_pos hDS (sub_pos.mpr hc_lt_w)
            have := mul_le_mul_of_nonneg_left hg1 hρ0.le
            have := mul_le_mul_of_nonneg_left hb1 h1ρ.le
            linarith

private lemma clause2_p2 (P : Params) (hStand : P.Standing) (hFocus : P.Focus) :
    ∃ Q'' : ℝ, P.θH / P.θL * P.αb - P.αg < Q'' ∧ Q'' < 1 - P.αg ∧
      ∀ Q₁ Q₂ : ℝ, ∀ e₁ e₂ : Outcome, Q'' ≤ Q₁ → Q₁ < Q₂ →
        IsEquilibrium P Q₁ e₁ → IsEquilibrium P Q₂ e₂ → e₂.πS ≤ e₁.πS := by
  obtain ⟨_, _, _, _, _, _, _, hcut_neg, _⟩ := standing_focus_p2 P hStand hFocus
  obtain ⟨gap, hgap_pos, hgap⟩ := tie_gap_p2 P hStand hFocus
  have h1ag_pos : 0 < 1 - P.αg := sub_pos.mpr hStand.2.2.2.2.2.2.2.2
  let M := max P.V_OO (P.V_OS (1 - P.αg) - gap)
  have hM_lt_top : M < P.V_OS (1 - P.αg) :=
    max_lt (voo_lt_vos_top_p2 P hStand hFocus) (by linarith)
  have hex_Q'' : ∃ Q'' : ℝ, 0 ≤ Q'' ∧ Q'' < 1 - P.αg ∧ M < P.V_OS Q'' := by
    rcases lt_or_ge M (P.V_OS 0) with hM0 | hM0
    · refine ⟨(1 - P.αg) / 2, (half_pos h1ag_pos).le, half_lt_self h1ag_pos,
        lt_of_lt_of_le hM0 (vos_mono_p2 P hStand hFocus (le_refl 0) (half_pos h1ag_pos).le)⟩
    · let tgt := (M + P.V_OS (1 - P.αg)) / 2
      have htgt_def : tgt = (M + P.V_OS (1 - P.αg)) / 2 := rfl
      obtain ⟨Q'', hQ''_mem, hQ''_eq⟩ := intermediate_value_Icc h1ag_pos.le
        (vos_continuousOn_p2 P hStand hFocus) ⟨by linarith, by linarith⟩
      refine ⟨Q'', hQ''_mem.1, ?_, by linarith⟩
      rcases eq_or_lt_of_le hQ''_mem.2 with rfl | hlt
      · exfalso; linarith
      · exact hlt
  obtain ⟨Q'', hQ''0, hQ''_hi, hM_lt⟩ := hex_Q''
  refine ⟨Q'', lt_of_lt_of_le hcut_neg hQ''0, hQ''_hi,
    fun Q₁ Q₂ e₁ e₂ hQ₁_ge hQlt he₁ he₂ => ?_⟩
  have h0₁ : 0 ≤ Q₁ := le_trans hQ''0 hQ₁_ge
  have h0₂ : 0 ≤ Q₂ := le_trans h0₁ hQlt.le
  have hπS₁ := piS_zero_above_p2 P hStand hFocus hgap h0₁
    (lt_of_lt_of_le hM_lt (vos_mono_p2 P hStand hFocus hQ''0 hQ₁_ge)) he₁
  have hπS₂ := piS_zero_above_p2 P hStand hFocus hgap h0₂
    (lt_of_lt_of_le hM_lt (vos_mono_p2 P hStand hFocus hQ''0 (le_trans hQ₁_ge hQlt.le))) he₂
  rw [hπS₁, hπS₂]

private lemma clause3_p2 :
    let P₀ : Params := ⟨3, 1, 1 / 2, 1 / 100, 1 / 10, 1⟩
    P₀.Dom ∧
      (∃ e : Outcome, IsEquilibrium P₀ 0 e) ∧
      (∃ e : Outcome, IsEquilibrium P₀ (2 / 5) e) ∧
      ∀ e₀ e₁ : Outcome, IsEquilibrium P₀ 0 e₀ →
        IsEquilibrium P₀ (2 / 5) e₁ →
        e₁.πS = 0 ∧ 0 < e₀.πS ∧ e₀.πR < e₁.πR := by
  let P₀ : Params := ⟨3, 1, 1 / 2, 1 / 100, 1 / 10, 1⟩
  have hDom : P₀.Dom := by
    unfold Params.Dom Params.Standing Params.Focus Params.HighOnlyDominated
    dsimp [P₀]; norm_num
  have htb0 := table_B P₀ hDom 0 (by norm_num) (by dsimp [P₀]; norm_num)
  have htb1 := table_B P₀ hDom (2 / 5) (by norm_num) (by dsimp [P₀]; norm_num)
  refine ⟨hDom, htb0.1, htb1.1, fun e₀ e₁ he₀ he₁ => ?_⟩
  have hvos0_lt : P₀.V_OS 0 < P₀.V_OO := by
    unfold Params.V_OS Params.V_OO Params.X Params.Y Params.supplyS
    dsimp [P₀]; norm_num
  have hvoo_lt : P₀.V_OO < P₀.V_OS (2 / 5) := by
    unfold Params.V_OS Params.V_OO Params.X Params.Y Params.supplyS
    dsimp [P₀]; norm_num
  rcases htb0.2 e₀ he₀ with h1 | h2
  · exfalso; linarith [h1.1]
  · rcases htb1.2 e₁ he₁ with g1 | g2
    · refine ⟨g1.2.2.1, ?_, ?_⟩
      · rw [h2.2.2.1]; unfold Params.X Params.Y; dsimp [P₀]; norm_num
      · rw [h2.2.1, g1.2.1]; exact hvoo_lt
    · exfalso; linarith [g2.1]

theorem solution :
    (∀ P : Params, P.Standing → P.Focus → ∀ Q₁ Q₂ : ℝ, ∀ e₁ e₂ : Outcome, 0 ≤ Q₁ → Q₁ < Q₂ →
      IsEquilibrium P Q₁ e₁ → IsEquilibrium P Q₂ e₂ → e₁.πR ≤ e₂.πR) ∧
    (∀ P : Params, P.Standing → P.Focus → ∃ Q'' : ℝ, P.θH / P.θL * P.αb - P.αg < Q'' ∧ Q'' < 1 - P.αg ∧
      ∀ Q₁ Q₂ : ℝ, ∀ e₁ e₂ : Outcome, Q'' ≤ Q₁ → Q₁ < Q₂ →
        IsEquilibrium P Q₁ e₁ → IsEquilibrium P Q₂ e₂ → e₂.πS ≤ e₁.πS) ∧
    ((⟨3, 1, 1 / 2, 1 / 100, 1 / 10, 1⟩ : Params).Dom ∧
      (∃ e : Outcome, IsEquilibrium ⟨3, 1, 1 / 2, 1 / 100, 1 / 10, 1⟩ 0 e) ∧
      (∃ e : Outcome, IsEquilibrium ⟨3, 1, 1 / 2, 1 / 100, 1 / 10, 1⟩ (2 / 5) e) ∧
      ∀ e₀ e₁ : Outcome, IsEquilibrium ⟨3, 1, 1 / 2, 1 / 100, 1 / 10, 1⟩ 0 e₀ →
        IsEquilibrium ⟨3, 1, 1 / 2, 1 / 100, 1 / 10, 1⟩ (2 / 5) e₁ →
        e₁.πS = 0 ∧ 0 < e₀.πS ∧ e₀.πR < e₁.πR) :=
  ⟨clause1_p2, clause2_p2, clause3_p2⟩
