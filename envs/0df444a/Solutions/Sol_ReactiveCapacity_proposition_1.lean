-- Prove2me | solution 1 for ReactiveCapacity.proposition_1
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-12T05:12:06.160982+00:00
-- url     : https://prove2.me/submissions/ad38f455-4654-4723-989f-2dfc96c86478

import Mathlib
import Definitions.Def_ReactiveCapacity_Model
import Definitions.Def_ReactiveCapacity_Game
import Definitions.Def_ReactiveCapacity_ClosedForms
import Theorems.Thm_ReactiveCapacity_table_B
import Theorems.Thm_ReactiveCapacity_table_C

open ReactiveCapacity

private lemma standing_aux_p1 (P : Params) (hStand : P.Standing) :
    0 < P.θH ∧ 0 < P.αg ∧ P.αb < P.αg ∧ 0 < 1 - P.ρ ∧ 0 < P.ρ * P.αg + 1 - P.ρ := by
  rcases hStand with ⟨hθL, hθLH, _hk, hρ0, hρ1, _hαb0, hαb_lt, hαg_gt, _hαg1⟩
  have hθH : 0 < P.θH := lt_trans hθL hθLH
  have hαg0 : 0 < P.αg := pos_of_mul_pos_left (lt_trans hθL hαg_gt) hθH.le
  have hαb_αg : P.αb < P.αg := lt_of_mul_lt_mul_right (lt_trans hαb_lt hαg_gt) hθH.le
  have h1ρ : 0 < 1 - P.ρ := sub_pos.mpr hρ1
  have hD1 : 0 < P.ρ * P.αg + 1 - P.ρ := by
    have : 0 < P.ρ * P.αg := mul_pos hρ0 hαg0
    linarith
  exact ⟨hθH, hαg0, hαb_αg, h1ρ, hD1⟩

private lemma y_pos_p1 (P : Params) (hStand : P.Standing) {S : ℝ} (hS : 0 ≤ S) :
    0 < P.Y S := by
  obtain ⟨hθH, hαg0, _, h1ρ, _⟩ := standing_aux_p1 P hStand
  rcases hStand with ⟨hθL, _, _, hρ0, _, _, _, _, _⟩
  unfold Params.Y
  have hden : 0 < P.ρ * P.αg + (1 - P.ρ) * S :=
    add_pos_of_pos_of_nonneg (mul_pos hρ0 hαg0) (mul_nonneg h1ρ.le hS)
  have hnum : 0 < P.ρ * P.αg * P.θH + (1 - P.ρ) * S * P.θL :=
    add_pos_of_pos_of_nonneg (mul_pos (mul_pos hρ0 hαg0) hθH)
      (mul_nonneg (mul_nonneg h1ρ.le hS) hθL.le)
  exact div_pos hnum hden

private lemma y_antitone_p1 (P : Params) (hStand : P.Standing) {S₁ S₂ : ℝ}
    (hS₁ : 0 ≤ S₁) (hle : S₁ ≤ S₂) :
    P.Y S₂ ≤ P.Y S₁ := by
  obtain ⟨_, hαg0, _, h1ρ, _⟩ := standing_aux_p1 P hStand
  rcases hStand with ⟨_, hθLH, _, hρ0, _, _, _, _, _⟩
  unfold Params.Y
  have hu₁ : 0 < P.ρ * P.αg + (1 - P.ρ) * S₁ :=
    add_pos_of_pos_of_nonneg (mul_pos hρ0 hαg0) (mul_nonneg h1ρ.le hS₁)
  have hu₂ : 0 < P.ρ * P.αg + (1 - P.ρ) * S₂ :=
    add_pos_of_pos_of_nonneg (mul_pos hρ0 hαg0) (mul_nonneg h1ρ.le (le_trans hS₁ hle))
  rw [div_le_div_iff₀ hu₂ hu₁]
  have hdiff :
      (P.ρ * P.αg * P.θH + (1 - P.ρ) * S₁ * P.θL) * (P.ρ * P.αg + (1 - P.ρ) * S₂) -
        (P.ρ * P.αg * P.θH + (1 - P.ρ) * S₂ * P.θL) * (P.ρ * P.αg + (1 - P.ρ) * S₁) =
        P.ρ * P.αg * (1 - P.ρ) * (P.θH - P.θL) * (S₂ - S₁) := by ring
  have hnonneg : 0 ≤ P.ρ * P.αg * (1 - P.ρ) * (P.θH - P.θL) * (S₂ - S₁) :=
    mul_nonneg
      (mul_nonneg (mul_nonneg (mul_nonneg hρ0.le hαg0.le) h1ρ.le) (sub_pos.mpr hθLH).le)
      (sub_nonneg.mpr hle)
  linarith

private lemma vos_strict_mono_p1 (P : Params) (hStand : P.Standing) (hFocus : P.Focus)
    {Q₁ Q₂ : ℝ} (h0 : 0 ≤ Q₁) (hlt : Q₁ < Q₂) (h1 : Q₂ ≤ 1 - P.αg) :
    P.V_OS Q₁ < P.V_OS Q₂ := by
  obtain ⟨hθH, hαg0, hαb_αg, h1ρ, _⟩ := standing_aux_p1 P hStand
  rcases hStand with ⟨hθL, hθLH, hk, hρ0, _, hαb0, _, _, _⟩
  have hFocus' : P.ρ * (P.θH - P.θL) < P.θL := by
    unfold Params.Focus at hFocus
    have h1 : 2 * (P.θL * P.αg - P.θH * P.αb) < 2 * P.θL * (P.αg - P.αb) := by
      have : 0 < (P.θH - P.θL) * P.αb := mul_pos (sub_pos.mpr hθLH) hαb0
      linarith
    have h2 : P.ρ * P.θH + (1 - P.ρ) * P.θL < 2 * P.θL :=
      lt_of_mul_lt_mul_right (lt_trans hFocus h1) (sub_pos.mpr hαb_αg).le
    linarith
  let C := P.ρ * P.αg * (P.θH - P.θL)
  have hC_pos : 0 < C := mul_pos (mul_pos hρ0 hαg0) (sub_pos.mpr hθLH)
  have hC_lt : C < P.αg * P.θL := by
    dsimp [C]
    have := mul_lt_mul_of_pos_right hFocus' hαg0
    linarith
  have hS₁_eq : P.supplyS Q₁ = P.αg + Q₁ := min_eq_left (by linarith)
  have hS₂_eq : P.supplyS Q₂ = P.αg + Q₂ := min_eq_left (by linarith)
  let u₁ := P.ρ * P.αg + (1 - P.ρ) * (P.αg + Q₁)
  let u₂ := P.ρ * P.αg + (1 - P.ρ) * (P.αg + Q₂)
  have hu₁_ge : P.αg ≤ u₁ := by
    have : 0 ≤ (1 - P.ρ) * Q₁ := mul_nonneg h1ρ.le h0
    dsimp [u₁]; linarith
  have hu₁_pos : 0 < u₁ := lt_of_lt_of_le hαg0 hu₁_ge
  have hu₁_lt_u₂ : u₁ < u₂ := by
    have := mul_lt_mul_of_pos_left hlt h1ρ
    dsimp [u₁, u₂]; linarith
  have hu₂_pos : 0 < u₂ := lt_trans hu₁_pos hu₁_lt_u₂
  have hV₁ : P.V_OS Q₁ = (C + u₁ * P.θL) ^ 2 / (u₁ * (4 * P.k)) := by
    unfold Params.V_OS Params.Y
    rw [hS₁_eq]
    change u₁ * ((P.ρ * P.αg * P.θH + (1 - P.ρ) * (P.αg + Q₁) * P.θL) / u₁) ^ 2 / (4 * P.k) = _
    have hnum : P.ρ * P.αg * P.θH + (1 - P.ρ) * (P.αg + Q₁) * P.θL = C + u₁ * P.θL := by
      dsimp [C, u₁]; ring
    rw [hnum]
    field_simp [hu₁_pos.ne', hk.ne']
  have hV₂ : P.V_OS Q₂ = (C + u₂ * P.θL) ^ 2 / (u₂ * (4 * P.k)) := by
    unfold Params.V_OS Params.Y
    rw [hS₂_eq]
    change u₂ * ((P.ρ * P.αg * P.θH + (1 - P.ρ) * (P.αg + Q₂) * P.θL) / u₂) ^ 2 / (4 * P.k) = _
    have hnum : P.ρ * P.αg * P.θH + (1 - P.ρ) * (P.αg + Q₂) * P.θL = C + u₂ * P.θL := by
      dsimp [C, u₂]; ring
    rw [hnum]
    field_simp [hu₂_pos.ne', hk.ne']
  rw [hV₁, hV₂, div_lt_div_iff₀ (mul_pos hu₁_pos (by linarith)) (mul_pos hu₂_pos (by linarith))]
  have hC_lt_u₁ : C < u₁ * P.θL :=
    lt_of_lt_of_le hC_lt (mul_le_mul_of_nonneg_right hu₁_ge hθL.le)
  have hC_lt_u₂ : C < u₂ * P.θL :=
    lt_trans hC_lt_u₁ (mul_lt_mul_of_pos_right hu₁_lt_u₂ hθL)
  have hC2_lt : C ^ 2 < u₁ * u₂ * P.θL ^ 2 := by
    have := mul_lt_mul'' hC_lt_u₁ hC_lt_u₂ hC_pos.le hC_pos.le
    linarith [show (u₁ * P.θL) * (u₂ * P.θL) = u₁ * u₂ * P.θL ^ 2 by ring]
  have hid :
      (C + u₂ * P.θL) ^ 2 * (u₁ * (4 * P.k)) - (C + u₁ * P.θL) ^ 2 * (u₂ * (4 * P.k)) =
        4 * P.k * (u₂ - u₁) * (u₁ * u₂ * P.θL ^ 2 - C ^ 2) := by ring
  have hpos : 0 < 4 * P.k * (u₂ - u₁) * (u₁ * u₂ * P.θL ^ 2 - C ^ 2) :=
    mul_pos (mul_pos (by linarith) (sub_pos.mpr hu₁_lt_u₂)) (sub_pos.mpr hC2_lt)
  linarith

private lemma voo_lt_vos_top_p1 (P : Params) (hStand : P.Standing) :
    P.V_OO < P.V_OS (1 - P.αg) := by
  obtain ⟨_, _, _, _, hD1⟩ := standing_aux_p1 P hStand
  have hX_pos : 0 < P.X := y_pos_p1 P hStand zero_le_one
  rcases hStand with ⟨_, _, hk, hρ0, _, _, _, _, _⟩
  have hS1 : P.supplyS (1 - P.αg) = 1 := by
    unfold Params.supplyS
    rw [show P.αg + (1 - P.αg) = 1 by ring, min_self]
  unfold Params.V_OO Params.V_OS
  rw [hS1]
  change (1 - P.ρ) * (P.ρ * P.αg + 1 - P.ρ) * P.X ^ 2 / (4 * P.k) <
    (P.ρ * P.αg + (1 - P.ρ) * 1) * P.X ^ 2 / (4 * P.k)
  refine div_lt_div_of_pos_right ?_ (by linarith)
  have hpos : 0 < P.ρ * (P.ρ * P.αg + 1 - P.ρ) * P.X ^ 2 :=
    mul_pos (mul_pos hρ0 hD1) (pow_pos hX_pos 2)
  linarith

private lemma vos_continuousOn_p1 (P : Params) (hStand : P.Standing) :
    ContinuousOn P.V_OS (Set.Icc 0 (1 - P.αg)) := by
  obtain ⟨_, hαg0, _, h1ρ, _⟩ := standing_aux_p1 P hStand
  rcases hStand with ⟨_, _, hk, hρ0, _, _, _, _, _⟩
  have hsupp_cont : Continuous P.supplyS :=
    (continuous_const.add continuous_id).min continuous_const
  have hden_ne : ∀ Q ∈ Set.Icc 0 (1 - P.αg), P.ρ * P.αg + (1 - P.ρ) * P.supplyS Q ≠ 0 := by
    intro Q hQ
    have hS0 : 0 ≤ P.supplyS Q := le_min (by linarith [hQ.1]) zero_le_one
    have hpos : 0 < P.ρ * P.αg + (1 - P.ρ) * P.supplyS Q :=
      add_pos_of_pos_of_nonneg (mul_pos hρ0 hαg0) (mul_nonneg h1ρ.le hS0)
    exact hpos.ne'
  have hnum_cont : Continuous (fun Q => P.ρ * P.αg * P.θH + (1 - P.ρ) * P.supplyS Q * P.θL) :=
    continuous_const.add ((continuous_const.mul hsupp_cont).mul continuous_const)
  have hden_cont : Continuous (fun Q => P.ρ * P.αg + (1 - P.ρ) * P.supplyS Q) :=
    continuous_const.add (continuous_const.mul hsupp_cont)
  have hY_cont : ContinuousOn (fun Q => P.Y (P.supplyS Q)) (Set.Icc 0 (1 - P.αg)) :=
    hnum_cont.continuousOn.div hden_cont.continuousOn hden_ne
  exact ((hden_cont.continuousOn.mul (hY_cont.pow 2)).div_const (4 * P.k))

private lemma eq_high_branch_p1 (P : Params) (hP : P.Dom) {Q : ℝ} (h0 : 0 ≤ Q)
    (hgt_oo : Q ≤ 1 - P.αg → P.V_OO < P.V_OS Q) {e : Outcome} (he : IsEquilibrium P Q e) :
    e.q = P.Y (P.supplyS Q) / (2 * P.k) ∧
    e.w = P.Y (P.supplyS Q) ^ 2 / (4 * P.k) ∧
    e.p .good = P.Y (P.supplyS Q) * P.θH / (2 * P.k) ∧
    e.p .bad = P.Y (P.supplyS Q) * P.θL / (2 * P.k) := by
  rcases le_or_gt Q (1 - P.αg) with hle | hgt
  · have hS : P.supplyS Q = P.αg + Q := min_eq_left (by linarith)
    rw [hS]
    rcases (table_B P hP Q h0 hle).2 e he with h1 | h2
    · exact ⟨h1.2.2.2.1, h1.2.2.2.2.1, h1.2.2.2.2.2.1, h1.2.2.2.2.2.2.1⟩
    · exfalso
      exact not_lt_of_ge h2.1 (hgt_oo hle)
  · have hS : P.supplyS Q = 1 := min_eq_right (by linarith)
    rw [hS]
    have htc := (table_C P hP Q hgt.le).2 e he
    exact ⟨htc.2.2.1, htc.2.2.2.1, htc.2.2.2.2.1, htc.2.2.2.2.2.1⟩

private lemma dec_above_p1 (P : Params) (hP : P.Dom) {Q₁ Q₂ : ℝ} (h0 : 0 ≤ Q₁) (hlt : Q₁ < Q₂)
    (hgt1 : Q₁ ≤ 1 - P.αg → P.V_OO < P.V_OS Q₁)
    (hgt2 : Q₂ ≤ 1 - P.αg → P.V_OO < P.V_OS Q₂)
    {e₁ e₂ : Outcome} (he₁ : IsEquilibrium P Q₁ e₁) (he₂ : IsEquilibrium P Q₂ e₂) :
    e₂.q ≤ e₁.q ∧ e₂.w ≤ e₁.w ∧ ∀ s : State, e₂.p s ≤ e₁.p s := by
  obtain ⟨hq₁, hw₁, hpg₁, hpb₁⟩ := eq_high_branch_p1 P hP h0 hgt1 he₁
  obtain ⟨hq₂, hw₂, hpg₂, hpb₂⟩ := eq_high_branch_p1 P hP (by linarith) hgt2 he₂
  have hStand : P.Standing := hP.1
  obtain ⟨hθH, hαg0, _, _, _⟩ := standing_aux_p1 P hStand
  rcases hStand with ⟨hθL, _, hk, _, _, _, _, _, _⟩
  have hS₁0 : 0 ≤ P.supplyS Q₁ := le_min (by linarith) zero_le_one
  have hS₂0 : 0 ≤ P.supplyS Q₂ := le_min (by linarith) zero_le_one
  have hSle : P.supplyS Q₁ ≤ P.supplyS Q₂ := min_le_min_right 1 (by linarith)
  have hYle : P.Y (P.supplyS Q₂) ≤ P.Y (P.supplyS Q₁) := y_antitone_p1 P hP.1 hS₁0 hSle
  have hY₂_pos : 0 < P.Y (P.supplyS Q₂) := y_pos_p1 P hP.1 hS₂0
  have h2k : 0 < 2 * P.k := by linarith
  have h4k : 0 < 4 * P.k := by linarith
  refine ⟨?_, ?_, ?_⟩
  · rw [hq₁, hq₂]
    exact div_le_div_of_nonneg_right hYle h2k.le
  · rw [hw₁, hw₂]
    have hsq : P.Y (P.supplyS Q₂) ^ 2 ≤ P.Y (P.supplyS Q₁) ^ 2 :=
      pow_le_pow_left₀ hY₂_pos.le hYle 2
    exact div_le_div_of_nonneg_right hsq h4k.le
  · rintro (_ | _)
    · rw [hpg₁, hpg₂]
      exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hYle hθH.le) h2k.le
    · rw [hpb₁, hpb₂]
      exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hYle hθL.le) h2k.le

private lemma clause2_p1 (P : Params) (hP : P.Dom) :
    ∃ Q' : ℝ, Q' < 1 ∧
      ∀ Q₁ Q₂ : ℝ, ∀ e₁ e₂ : Outcome, Q₁ < Q₂ → IsEquilibrium P Q₁ e₁ → IsEquilibrium P Q₂ e₂ →
        (0 ≤ Q₁ → Q₂ ≤ Q' → e₁.q ≤ e₂.q ∧ e₁.w ≤ e₂.w ∧ ∀ s : State, e₁.p s ≤ e₂.p s) ∧
        (Q' < Q₁ → e₂.q ≤ e₁.q ∧ e₂.w ≤ e₁.w ∧ ∀ s : State, e₂.p s ≤ e₁.p s) := by
  have hStand : P.Standing := hP.1
  have hFocus : P.Focus := hP.2.1
  obtain ⟨hθH, hαg0, _, h1ρ, _⟩ := standing_aux_p1 P hStand
  rcases hStand with ⟨hθL, _, hk, hρ0, hρ1, _, _, _, hαg1⟩
  rcases le_or_gt P.V_OO (P.V_OS 0) with hoo_le | hos_lt
  · refine ⟨0, zero_lt_one, fun Q₁ Q₂ e₁ e₂ hlt he₁ he₂ => ⟨?_, ?_⟩⟩
    · intro h0 hQ₂
      exfalso; linarith
    · intro hQ₁_pos
      exact dec_above_p1 P hP hQ₁_pos.le hlt
        (fun hle => lt_of_le_of_lt hoo_le (vos_strict_mono_p1 P hP.1 hFocus (le_refl 0) hQ₁_pos hle))
        (fun hle => lt_of_le_of_lt hoo_le
          (vos_strict_mono_p1 P hP.1 hFocus (le_refl 0) (lt_trans hQ₁_pos hlt) hle))
        he₁ he₂
  · have htop : P.V_OO < P.V_OS (1 - P.αg) := voo_lt_vos_top_p1 P hP.1
    have h1ag_pos : 0 ≤ 1 - P.αg := by linarith
    obtain ⟨Q', hQ'_mem, hQ'_eq⟩ := intermediate_value_Icc h1ag_pos (vos_continuousOn_p1 P hP.1)
      ⟨hos_lt.le, htop.le⟩
    rcases hQ'_mem with ⟨hQ'0, hQ'1⟩
    refine ⟨Q', by linarith, fun Q₁ Q₂ e₁ e₂ hlt he₁ he₂ => ⟨?_, ?_⟩⟩
    · intro h0 hQ₂_le
      have hQ₁_lt_Q' : Q₁ < Q' := lt_of_lt_of_le hlt hQ₂_le
      have hvos_Q₁ : P.V_OS Q₁ < P.V_OO := by
        rw [← hQ'_eq]
        exact vos_strict_mono_p1 P hP.1 hFocus h0 hQ₁_lt_Q' hQ'1
      have htb₁ := (table_B P hP Q₁ h0 (by linarith)).2 e₁ he₁
      have he₁_oo :
          e₁.q = (1 - P.ρ) * P.X / (2 * P.k) ∧
          e₁.w = (1 - P.ρ) * P.X ^ 2 / (4 * P.k) ∧
          e₁.p .good = (1 - P.ρ) * P.X * P.θH / (2 * P.k) ∧
          e₁.p .bad = (1 - P.ρ) * P.X * P.θL / (2 * P.k) := by
        rcases htb₁ with h1 | h2
        · exfalso; linarith [h1.1]
        · exact ⟨h2.2.2.2.1, h2.2.2.2.2.1, h2.2.2.2.2.2.1, h2.2.2.2.2.2.2.1⟩
      rcases (table_B P hP Q₂ (by linarith) (by linarith)).2 e₂ he₂ with h1 | h2
      · have hX_pos : 0 < P.X := y_pos_p1 P hP.1 zero_le_one
        have hX_le_Y : P.X ≤ P.Y (P.αg + Q₂) :=
          y_antitone_p1 P hP.1 (by linarith) (by linarith : P.αg + Q₂ ≤ 1)
        have h1ρX_le : (1 - P.ρ) * P.X ≤ P.Y (P.αg + Q₂) :=
          le_trans (mul_le_of_le_one_left hX_pos.le (by linarith)) hX_le_Y
        have h1ρX2_le : (1 - P.ρ) * P.X ^ 2 ≤ P.Y (P.αg + Q₂) ^ 2 :=
          le_trans (mul_le_of_le_one_left (sq_nonneg _) (by linarith))
            (pow_le_pow_left₀ hX_pos.le hX_le_Y 2)
        have h2k : 0 < 2 * P.k := by linarith
        have h4k : 0 < 4 * P.k := by linarith
        refine ⟨?_, ?_, ?_⟩
        · rw [he₁_oo.1, h1.2.2.2.1]
          exact div_le_div_of_nonneg_right h1ρX_le h2k.le
        · rw [he₁_oo.2.1, h1.2.2.2.2.1]
          exact div_le_div_of_nonneg_right h1ρX2_le h4k.le
        · rintro (_ | _)
          · rw [he₁_oo.2.2.1, h1.2.2.2.2.2.1]
            exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right h1ρX_le hθH.le) h2k.le
          · rw [he₁_oo.2.2.2, h1.2.2.2.2.2.2.1]
            exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right h1ρX_le hθL.le) h2k.le
      · refine ⟨?_, ?_, ?_⟩
        · rw [he₁_oo.1, h2.2.2.2.1]
        · rw [he₁_oo.2.1, h2.2.2.2.2.1]
        · rintro (_ | _)
          · rw [he₁_oo.2.2.1, h2.2.2.2.2.2.1]
          · rw [he₁_oo.2.2.2, h2.2.2.2.2.2.2.1]
    · intro hQ'_lt
      exact dec_above_p1 P hP (by linarith) hlt
        (fun hle => by rw [← hQ'_eq]; exact vos_strict_mono_p1 P hP.1 hFocus hQ'0 hQ'_lt hle)
        (fun hle => by
          rw [← hQ'_eq]
          exact vos_strict_mono_p1 P hP.1 hFocus hQ'0 (lt_trans hQ'_lt hlt) hle)
        he₁ he₂

private lemma clause3_p1 :
    let P₀ : Params := ⟨3, 1, 1 / 2, 1 / 100, 1 / 10, 1⟩
    P₀.Dom ∧
      ∀ e₀ e₁ e₂ : Outcome, IsEquilibrium P₀ 0 e₀ →
        IsEquilibrium P₀ (2 / 5) e₁ →
        IsEquilibrium P₀ (1 / 2) e₂ →
        e₀.q < e₁.q ∧ e₂.q < e₁.q ∧ e₀.w < e₁.w ∧ e₂.w < e₁.w ∧
        ∀ s : State, e₀.p s < e₁.p s ∧ e₂.p s < e₁.p s := by
  let P₀ : Params := ⟨3, 1, 1 / 2, 1 / 100, 1 / 10, 1⟩
  have hDom : P₀.Dom := by
    unfold Params.Dom Params.Standing Params.Focus Params.HighOnlyDominated
    dsimp [P₀]
    norm_num
  refine ⟨hDom, fun e₀ e₁ e₂ he₀ he₁ he₂ => ?_⟩
  have hvos0_lt : P₀.V_OS 0 < P₀.V_OO := by
    unfold Params.V_OS Params.V_OO Params.X Params.Y Params.supplyS
    dsimp [P₀]
    norm_num
  have hvoo_lt : P₀.V_OO < P₀.V_OS (2 / 5) := by
    unfold Params.V_OS Params.V_OO Params.X Params.Y Params.supplyS
    dsimp [P₀]
    norm_num
  have htb₀ := (table_B P₀ hDom 0 (by norm_num) (by dsimp [P₀]; norm_num)).2 e₀ he₀
  have htb₁ := (table_B P₀ hDom (2 / 5) (by norm_num) (by dsimp [P₀]; norm_num)).2 e₁ he₁
  have htc₂ := (table_C P₀ hDom (1 / 2) (by dsimp [P₀]; norm_num)).2 e₂ he₂
  have he₀_vals :
      e₀.q = (1 - P₀.ρ) * P₀.X / (2 * P₀.k) ∧
      e₀.w = (1 - P₀.ρ) * P₀.X ^ 2 / (4 * P₀.k) ∧
      e₀.p .good = (1 - P₀.ρ) * P₀.X * P₀.θH / (2 * P₀.k) ∧
      e₀.p .bad = (1 - P₀.ρ) * P₀.X * P₀.θL / (2 * P₀.k) := by
    rcases htb₀ with h1 | h2
    · exfalso; linarith [h1.1]
    · exact ⟨h2.2.2.2.1, h2.2.2.2.2.1, h2.2.2.2.2.2.1, h2.2.2.2.2.2.2.1⟩
  have he₁_vals :
      e₁.q = P₀.Y (P₀.αg + 2 / 5) / (2 * P₀.k) ∧
      e₁.w = P₀.Y (P₀.αg + 2 / 5) ^ 2 / (4 * P₀.k) ∧
      e₁.p .good = P₀.Y (P₀.αg + 2 / 5) * P₀.θH / (2 * P₀.k) ∧
      e₁.p .bad = P₀.Y (P₀.αg + 2 / 5) * P₀.θL / (2 * P₀.k) := by
    rcases htb₁ with h1 | h2
    · exact ⟨h1.2.2.2.1, h1.2.2.2.2.1, h1.2.2.2.2.2.1, h1.2.2.2.2.2.2.1⟩
    · exfalso; linarith [h2.1]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [he₀_vals.1, he₁_vals.1]; unfold Params.X Params.Y; dsimp [P₀]; norm_num
  · rw [htc₂.2.2.1, he₁_vals.1]; unfold Params.X Params.Y; dsimp [P₀]; norm_num
  · rw [he₀_vals.2.1, he₁_vals.2.1]; unfold Params.X Params.Y; dsimp [P₀]; norm_num
  · rw [htc₂.2.2.2.1, he₁_vals.2.1]; unfold Params.X Params.Y; dsimp [P₀]; norm_num
  · rintro (_ | _)
    · rw [he₀_vals.2.2.1, he₁_vals.2.2.1, htc₂.2.2.2.2.1]
      unfold Params.X Params.Y; dsimp [P₀]; norm_num
    · rw [he₀_vals.2.2.2, he₁_vals.2.2.2, htc₂.2.2.2.2.2.1]
      unfold Params.X Params.Y; dsimp [P₀]; norm_num

theorem solution :
    (∀ P : Params, P.Dom → ∀ Qbar : ℝ, 0 ≤ Qbar → ∃ e : Outcome, IsEquilibrium P Qbar e) ∧
    (∀ P : Params, P.Dom → ∃ Q' : ℝ, Q' < 1 ∧
      ∀ Q₁ Q₂ : ℝ, ∀ e₁ e₂ : Outcome, Q₁ < Q₂ → IsEquilibrium P Q₁ e₁ → IsEquilibrium P Q₂ e₂ →
        (0 ≤ Q₁ → Q₂ ≤ Q' → e₁.q ≤ e₂.q ∧ e₁.w ≤ e₂.w ∧ ∀ s : State, e₁.p s ≤ e₂.p s) ∧
        (Q' < Q₁ → e₂.q ≤ e₁.q ∧ e₂.w ≤ e₁.w ∧ ∀ s : State, e₂.p s ≤ e₁.p s)) ∧
    ((⟨3, 1, 1 / 2, 1 / 100, 1 / 10, 1⟩ : Params).Dom ∧
      ∀ e₀ e₁ e₂ : Outcome, IsEquilibrium ⟨3, 1, 1 / 2, 1 / 100, 1 / 10, 1⟩ 0 e₀ →
        IsEquilibrium ⟨3, 1, 1 / 2, 1 / 100, 1 / 10, 1⟩ (2 / 5) e₁ →
        IsEquilibrium ⟨3, 1, 1 / 2, 1 / 100, 1 / 10, 1⟩ (1 / 2) e₂ →
        e₀.q < e₁.q ∧ e₂.q < e₁.q ∧ e₀.w < e₁.w ∧ e₂.w < e₁.w ∧
        ∀ s : State, e₀.p s < e₁.p s ∧ e₂.p s < e₁.p s) := by
  refine ⟨?_, clause2_p1, clause3_p1⟩
  intro P hP Qbar h0
  rcases le_or_gt Qbar (1 - P.αg) with hle | hgt
  · exact (table_B P hP Qbar h0 hle).1
  · exact (table_C P hP Qbar hgt.le).1
