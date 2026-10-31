-- Prove2me | solution 1 for RobustBooking.BidPrice.theorem7_bid_price_competitive
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-10-30T23:11:03.808713+00:00
-- url     : https://prove2.me/submissions/b59466cb-59ca-471e-81c3-d26700f602c4

import Mathlib
import Definitions.Def_RobustBooking_BidPrice_Model
import Definitions.Def_RobustBooking_BidPrice_Policy
import Definitions.Def_RobustBooking_BidPrice_Controls
import Theorems.Thm_RobustBooking_BidPrice_lemma2_closed_forms
import Theorems.Thm_RobustBooking_BidPrice_eq5_order_quantity_le

namespace Aux_RB_thm7

open RobustBooking.BidPrice

-- Section 1: Basic properties of r, rho, Q, P, V
lemma discountRatio_bounds (fmin fmax : ℝ) (hfmin : 0 < fmin) (hf : fmin < fmax) :
    0 < discountRatio fmin fmax ∧ discountRatio fmin fmax < 1 := by
  have hfmax : 0 < fmax := lt_trans hfmin hf
  unfold discountRatio
  exact ⟨div_pos hfmin hfmax, (div_lt_one hfmax).mpr hf⟩

lemma log_discountRatio_neg (fmin fmax : ℝ) (hfmin : 0 < fmin) (hf : fmin < fmax) :
    Real.log (discountRatio fmin fmax) < 0 := by
  obtain ⟨hr0, hr1⟩ := discountRatio_bounds fmin fmax hfmin hf
  exact Real.log_neg hr0 hr1

lemma one_sub_log_gt_one (fmin fmax : ℝ) (hfmin : 0 < fmin) (hf : fmin < fmax) :
    1 < 1 - Real.log (discountRatio fmin fmax) := by
  have h := log_discountRatio_neg fmin fmax hfmin hf
  linarith

lemma one_sub_log_pos (fmin fmax : ℝ) (hfmin : 0 < fmin) (hf : fmin < fmax) :
    0 < 1 - Real.log (discountRatio fmin fmax) :=
  lt_trans zero_lt_one (one_sub_log_gt_one fmin fmax hfmin hf)

lemma rho_bounds (fmin fmax : ℝ) (hfmin : 0 < fmin) (hf : fmin < fmax) :
    0 < rho (discountRatio fmin fmax) ∧ rho (discountRatio fmin fmax) < 1 := by
  have h1 : 1 < 1 - Real.log (discountRatio fmin fmax) := one_sub_log_gt_one fmin fmax hfmin hf
  have h0 : 0 < 1 - Real.log (discountRatio fmin fmax) := lt_trans zero_lt_one h1
  unfold rho
  exact ⟨one_div_pos.mpr h0, (div_lt_one h0).mpr h1⟩

lemma rho_mul_one_sub_log (fmin fmax : ℝ) (hfmin : 0 < fmin) (hf : fmin < fmax) :
    rho (discountRatio fmin fmax) * (1 - Real.log (discountRatio fmin fmax)) = 1 := by
  have h0 : 1 - Real.log (discountRatio fmin fmax) ≠ 0 :=
    (one_sub_log_pos fmin fmax hfmin hf).ne'
  unfold rho
  exact one_div_mul_cancel h0

lemma log_diff_eq (fmin fmax : ℝ) (hfmin : 0 < fmin) (hf : fmin < fmax) :
    Real.log fmax - Real.log fmin = -Real.log (discountRatio fmin fmax) := by
  have hfmax : 0 < fmax := lt_trans hfmin hf
  unfold discountRatio
  rw [Real.log_div hfmin.ne' hfmax.ne']
  ring

lemma Q_closed_form (fmin fmax n : ℝ) (hfmin : 0 < fmin) (hf : fmin < fmax) (f : ℝ) :
    protectionControl fmin fmax n f =
      n - (Real.log fmax - Real.log f) * n / (1 - Real.log (discountRatio fmin fmax)) := by
  unfold protectionControl theta
  rw [log_diff_eq fmin fmax hfmin hf]
  have hL : Real.log (discountRatio fmin fmax) ≠ 0 := (log_discountRatio_neg fmin fmax hfmin hf).ne
  have h1L : 1 - Real.log (discountRatio fmin fmax) ≠ 0 := (one_sub_log_pos fmin fmax hfmin hf).ne'
  field_simp
  ring

lemma Q_fmax (fmin fmax n : ℝ) (hfmin : 0 < fmin) (hf : fmin < fmax) :
    protectionControl fmin fmax n fmax = n := by
  rw [Q_closed_form fmin fmax n hfmin hf fmax]
  simp

lemma Q_fmin (fmin fmax n : ℝ) (hfmin : 0 < fmin) (hf : fmin < fmax) :
    protectionControl fmin fmax n fmin = n * rho (discountRatio fmin fmax) := by
  rw [Q_closed_form fmin fmax n hfmin hf fmin, log_diff_eq fmin fmax hfmin hf]
  have h1L : 1 - Real.log (discountRatio fmin fmax) ≠ 0 := (one_sub_log_pos fmin fmax hfmin hf).ne'
  unfold rho
  field_simp
  ring

lemma Q_le_iff (fmin fmax n : ℝ) (hfmin : 0 < fmin) (hf : fmin < fmax) (hn : 0 < n)
    {f₁ f₂ : ℝ} (hf₁ : 0 < f₁) (hf₂ : 0 < f₂) :
    protectionControl fmin fmax n f₁ ≤ protectionControl fmin fmax n f₂ ↔ f₁ ≤ f₂ := by
  rw [Q_closed_form fmin fmax n hfmin hf f₁, Q_closed_form fmin fmax n hfmin hf f₂]
  have h1L : 0 < 1 - Real.log (discountRatio fmin fmax) := one_sub_log_pos fmin fmax hfmin hf
  constructor
  · intro hle
    have hlog : Real.log f₁ ≤ Real.log f₂ := by
      have hdiv : (Real.log fmax - Real.log f₂) * n / (1 - Real.log (discountRatio fmin fmax)) ≤
          (Real.log fmax - Real.log f₁) * n / (1 - Real.log (discountRatio fmin fmax)) := by
        linarith
      have hsub : (Real.log fmax - Real.log f₂) * n ≤ (Real.log fmax - Real.log f₁) * n :=
        (div_le_div_iff_of_pos_right h1L).mp hdiv
      have h2 := le_of_mul_le_mul_right hsub hn
      linarith
    exact (Real.log_le_log_iff hf₁ hf₂).mp hlog
  · intro hle
    have hlog : Real.log f₁ ≤ Real.log f₂ := (Real.log_le_log_iff hf₁ hf₂).mpr hle
    have hsub : (Real.log fmax - Real.log f₂) * n ≤ (Real.log fmax - Real.log f₁) * n :=
      mul_le_mul_of_nonneg_right (by linarith) hn.le
    have hdiv := div_le_div_of_nonneg_right hsub h1L.le
    linarith

lemma Q_bounds (fmin fmax n : ℝ) (hfmin : 0 < fmin) (hf : fmin < fmax) (hn : 0 < n)
    {f : ℝ} (hf_mem : f ∈ Set.Icc fmin fmax) :
    n * rho (discountRatio fmin fmax) ≤ protectionControl fmin fmax n f ∧
    protectionControl fmin fmax n f ≤ n := by
  have hf_pos : 0 < f := lt_of_lt_of_le hfmin hf_mem.1
  have hfmax_pos : 0 < fmax := lt_trans hfmin hf
  constructor
  · calc n * rho (discountRatio fmin fmax)
        = protectionControl fmin fmax n fmin := (Q_fmin fmin fmax n hfmin hf).symm
      _ ≤ protectionControl fmin fmax n f := (Q_le_iff fmin fmax n hfmin hf hn hfmin hf_pos).mpr hf_mem.1
  · calc protectionControl fmin fmax n f
        ≤ protectionControl fmin fmax n fmax := (Q_le_iff fmin fmax n hfmin hf hn hf_pos hfmax_pos).mpr hf_mem.2
      _ = n := Q_fmax fmin fmax n hfmin hf

lemma Q_nonneg (fmin fmax n : ℝ) (hfmin : 0 < fmin) (hf : fmin < fmax) (hn : 0 < n)
    {f : ℝ} (hf_mem : f ∈ Set.Icc fmin fmax) :
    0 ≤ protectionControl fmin fmax n f := by
  have hρ := (rho_bounds fmin fmax hfmin hf).1
  have hb := (Q_bounds fmin fmax n hfmin hf hn hf_mem).1
  nlinarith

lemma P_Q_eq (fmin fmax n : ℝ) (hfmin : 0 < fmin) (hf : fmin < fmax) (hn : 0 < n)
    {f : ℝ} (hf_mem : f ∈ Set.Icc fmin fmax) :
    bidPriceP fmin fmax n (protectionControl fmin fmax n f) = f := by
  apply le_antisymm
  · exact eq5_order_quantity_le fmin fmax (protectionControl fmin fmax n) f hf_mem
  · unfold bidPriceP orderQuantityControl
    have hne : {g : ℝ | g ∈ Set.Icc fmin fmax ∧ protectionControl fmin fmax n f ≤ protectionControl fmin fmax n g}.Nonempty :=
      ⟨f, hf_mem, le_rfl⟩
    apply le_csInf hne
    rintro g ⟨hg_mem, hQg⟩
    have hf_pos : 0 < f := lt_of_lt_of_le hfmin hf_mem.1
    have hg_pos : 0 < g := lt_of_lt_of_le hfmin hg_mem.1
    exact (Q_le_iff fmin fmax n hfmin hf hn hf_pos hg_pos).mp hQg

lemma V_Q_eq (fmin fmax n : ℝ) (hfmin : 0 < fmin) (hf : fmin < fmax) (hn : 0 < n)
    {f : ℝ} (hf_mem : f ∈ Set.Icc fmin fmax) :
    valueAccumulation fmin fmax n (protectionControl fmin fmax n f) =
      1 / (1 - Real.log (discountRatio fmin fmax)) * (f * n) := by
  obtain ⟨hQ1, hQ2⟩ := Q_bounds fmin fmax n hfmin hf hn hf_mem
  obtain ⟨_, hV⟩ := (lemma2_closed_forms fmin fmax n hfmin hf hn (protectionControl fmin fmax n f)).2 hQ1 hQ2
  rw [hV, P_Q_eq fmin fmax n hfmin hf hn hf_mem]
  ring

lemma P_in_Icc_and_Q_eq (fmin fmax n : ℝ) (hfmin : 0 < fmin) (hf : fmin < fmax) (hn : 0 < n)
    {s : ℝ} (hs0 : 0 ≤ s) (hsn : s ≤ n) :
    bidPriceP fmin fmax n s ∈ Set.Icc fmin fmax ∧
    s ≤ protectionControl fmin fmax n (bidPriceP fmin fmax n s) := by
  have hfmax : 0 < fmax := lt_trans hfmin hf
  obtain ⟨hr0, hr1⟩ := discountRatio_bounds fmin fmax hfmin hf
  obtain ⟨hρ0, hρ1⟩ := rho_bounds fmin fmax hfmin hf
  have h1L : 0 < 1 - Real.log (discountRatio fmin fmax) := one_sub_log_pos fmin fmax hfmin hf
  have hρL := rho_mul_one_sub_log fmin fmax hfmin hf
  by_cases hslt : s < n * rho (discountRatio fmin fmax)
  · obtain ⟨hP, _⟩ := (lemma2_closed_forms fmin fmax n hfmin hf hn s).1 hs0 hslt
    rw [hP]
    refine ⟨⟨le_rfl, hf.le⟩, ?_⟩
    rw [Q_fmin fmin fmax n hfmin hf]
    exact hslt.le
  · push_neg at hslt
    obtain ⟨hP, _⟩ := (lemma2_closed_forms fmin fmax n hfmin hf hn s).2 hslt hsn
    set r := discountRatio fmin fmax
    set ρ := rho r
    set c := n * (1 - ρ)
    have hc_pos : 0 < c := mul_pos hn (sub_pos.mpr hρ1)
    have hexp0 : 0 ≤ (n - s) / c := div_nonneg (by linarith) hc_pos.le
    have hexp1 : (n - s) / c ≤ 1 := by
      rw [div_le_one hc_pos]
      dsimp [c]
      linarith
    have hP_pos : 0 < bidPriceP fmin fmax n s := by
      rw [hP]
      exact mul_pos hfmax (Real.rpow_pos_of_pos hr0 _)
    have hrf : fmax * r = fmin := by
      dsimp [r, discountRatio]
      field_simp
    have hP_ge : fmin ≤ bidPriceP fmin fmax n s := by
      rw [hP]
      calc fmin = fmax * r ^ (1 : ℝ) := by rw [Real.rpow_one, hrf]
        _ ≤ fmax * r ^ ((n - s) / c) :=
          mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_ge hr0 hr1.le hexp1) hfmax.le
    have hP_le : bidPriceP fmin fmax n s ≤ fmax := by
      rw [hP]
      calc fmax * r ^ ((n - s) / c) ≤ fmax * r ^ (0 : ℝ) :=
            mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_ge hr0 hr1.le hexp0) hfmax.le
        _ = fmax := by simp
    refine ⟨⟨hP_ge, hP_le⟩, ?_⟩
    rw [Q_closed_form fmin fmax n hfmin hf, hP,
      Real.log_mul hfmax.ne' (Real.rpow_pos_of_pos hr0 _).ne', Real.log_rpow hr0]
    have hcL : c * (1 - Real.log r) = -Real.log r * n := by
      dsimp [c]
      linear_combination (-n) * hρL
    have hcalc : (Real.log fmax - (Real.log fmax + (n - s) / c * Real.log r)) * n / (1 - Real.log r) = n - s := by
      calc (Real.log fmax - (Real.log fmax + (n - s) / c * Real.log r)) * n / (1 - Real.log r)
          = (n - s) / c * (-Real.log r * n) / (1 - Real.log r) := by ring
        _ = (n - s) * (c / c) * ((1 - Real.log r) / (1 - Real.log r)) := by rw [← hcL]; ring
        _ = n - s := by rw [div_self hc_pos.ne', div_self h1L.ne', mul_one, mul_one]
    linarith

lemma P_le_iff_le_Q (fmin fmax n : ℝ) (hfmin : 0 < fmin) (hf : fmin < fmax) (hn : 0 < n)
    {s : ℝ} (hs0 : 0 ≤ s) (hsn : s ≤ n) {f : ℝ} (hf_mem : f ∈ Set.Icc fmin fmax) :
    bidPriceP fmin fmax n s ≤ f ↔ s ≤ protectionControl fmin fmax n f := by
  constructor
  · intro hPs
    obtain ⟨hP_mem, hs_le_QP⟩ := P_in_Icc_and_Q_eq fmin fmax n hfmin hf hn hs0 hsn
    have hP_pos : 0 < bidPriceP fmin fmax n s := lt_of_lt_of_le hfmin hP_mem.1
    have hf_pos : 0 < f := lt_of_lt_of_le hfmin hf_mem.1
    exact le_trans hs_le_QP ((Q_le_iff fmin fmax n hfmin hf hn hP_pos hf_pos).mpr hPs)
  · intro hsQ
    unfold bidPriceP orderQuantityControl
    exact csInf_le ⟨fmin, fun g hg => hg.1.1⟩ ⟨hf_mem, hsQ⟩

lemma P_mono (fmin fmax n : ℝ) (hfmin : 0 < fmin) (hf : fmin < fmax) (hn : 0 < n)
    {s₁ s₂ : ℝ} (hs₁ : 0 ≤ s₁) (hs : s₁ ≤ s₂) (hs₂ : s₂ ≤ n) :
    bidPriceP fmin fmax n s₁ ≤ bidPriceP fmin fmax n s₂ := by
  obtain ⟨hP2_mem, hs2_Q⟩ := P_in_Icc_and_Q_eq fmin fmax n hfmin hf hn (le_trans hs₁ hs) hs₂
  exact (P_le_iff_le_Q fmin fmax n hfmin hf hn hs₁ (le_trans hs hs₂) hP2_mem).mpr (le_trans hs hs2_Q)

-- Closed form & increment inequality for V
lemma V_zero (fmin fmax n : ℝ) : valueAccumulation fmin fmax n 0 = 0 := by
  simp [valueAccumulation]

lemma V_below_eq (fmin fmax n : ℝ) (hfmin : 0 < fmin) (hf : fmin < fmax) (hn : 0 < n)
    {q : ℝ} (hq0 : 0 ≤ q) (hq : q ≤ n * rho (discountRatio fmin fmax)) :
    valueAccumulation fmin fmax n q = q * fmin := by
  rcases hq.lt_or_eq with hlt | rfl
  · exact ((lemma2_closed_forms fmin fmax n hfmin hf hn q).1 hq0 hlt).2
  · rw [← Q_fmin fmin fmax n hfmin hf, V_Q_eq fmin fmax n hfmin hf hn ⟨le_rfl, hf.le⟩,
      Q_fmin fmin fmax n hfmin hf]
    unfold rho
    ring

lemma V_diff_le_P_mul_above (fmin fmax n : ℝ) (hfmin : 0 < fmin) (hf : fmin < fmax) (hn : 0 < n)
    {q₁ q₂ : ℝ} (hq₁ : n * rho (discountRatio fmin fmax) ≤ q₁) (hq : q₁ ≤ q₂) (hq₂ : q₂ ≤ n) :
    valueAccumulation fmin fmax n q₂ - valueAccumulation fmin fmax n q₁ ≤
      bidPriceP fmin fmax n q₂ * (q₂ - q₁) := by
  obtain ⟨hr0, hr1⟩ := discountRatio_bounds fmin fmax hfmin hf
  obtain ⟨hρ0, hρ1⟩ := rho_bounds fmin fmax hfmin hf
  have h1L : 0 < 1 - Real.log (discountRatio fmin fmax) := one_sub_log_pos fmin fmax hfmin hf
  have hρL := rho_mul_one_sub_log fmin fmax hfmin hf
  obtain ⟨hP1, hV1⟩ := (lemma2_closed_forms fmin fmax n hfmin hf hn q₁).2 hq₁ (le_trans hq hq₂)
  obtain ⟨hP2, hV2⟩ := (lemma2_closed_forms fmin fmax n hfmin hf hn q₂).2 (le_trans hq₁ hq) hq₂
  set r := discountRatio fmin fmax
  set ρ := rho r
  set c := n * (1 - ρ)
  have hc_pos : 0 < c := mul_pos hn (sub_pos.mpr hρ1)
  have hexp_split : (n - q₁) / c = (n - q₂) / c + (q₂ - q₁) / c := by ring
  have hP1_eq : bidPriceP fmin fmax n q₁ = bidPriceP fmin fmax n q₂ * r ^ ((q₂ - q₁) / c) := by
    rw [hP1, hP2]
    change fmax * r ^ ((n - q₁) / c) = fmax * r ^ ((n - q₂) / c) * r ^ ((q₂ - q₁) / c)
    rw [hexp_split, Real.rpow_add hr0, mul_assoc]
  have hc_eq : c = -(n * ρ * Real.log r) := by
    dsimp [c]
    linear_combination (-n) * hρL
  have hexp_log : Real.log r * ((q₂ - q₁) / c) = -((q₂ - q₁) / (n * ρ)) := by
    have hL_ne : Real.log r ≠ 0 := (log_discountRatio_neg fmin fmax hfmin hf).ne
    have hn_ne : n ≠ 0 := hn.ne'
    have hρ_ne : ρ ≠ 0 := hρ0.ne'
    rw [hc_eq]
    field_simp
  have hrpow_ge : 1 - (q₂ - q₁) / (n * ρ) ≤ r ^ ((q₂ - q₁) / c) := by
    rw [Real.rpow_def_of_pos hr0, hexp_log]
    have h := Real.add_one_le_exp (-((q₂ - q₁) / (n * ρ)))
    linarith
  have hP2_pos : 0 < bidPriceP fmin fmax n q₂ :=
    lt_of_lt_of_le hfmin (P_in_Icc_and_Q_eq fmin fmax n hfmin hf hn (by nlinarith) hq₂).1.1
  have hV1' : valueAccumulation fmin fmax n q₁ = n * ρ * bidPriceP fmin fmax n q₁ := by
    rw [hV1]; dsimp [ρ, rho]; ring
  have hV2' : valueAccumulation fmin fmax n q₂ = n * ρ * bidPriceP fmin fmax n q₂ := by
    rw [hV2]; dsimp [ρ, rho]; ring
  rw [hV1', hV2', hP1_eq]
  have hmul := mul_le_mul_of_nonneg_left hrpow_ge (by positivity : 0 ≤ n * ρ * bidPriceP fmin fmax n q₂)
  have hcancel : n * ρ * bidPriceP fmin fmax n q₂ * (1 - (q₂ - q₁) / (n * ρ)) =
      n * ρ * bidPriceP fmin fmax n q₂ - bidPriceP fmin fmax n q₂ * (q₂ - q₁) := by
    have hn_ne : n ≠ 0 := hn.ne'
    have hρ_ne : ρ ≠ 0 := hρ0.ne'
    field_simp
  linarith

lemma V_diff_le_P_mul (fmin fmax n : ℝ) (hfmin : 0 < fmin) (hf : fmin < fmax) (hn : 0 < n)
    {q₁ q₂ : ℝ} (hq₁ : 0 ≤ q₁) (hq : q₁ ≤ q₂) (hq₂ : q₂ ≤ n) :
    valueAccumulation fmin fmax n q₂ - valueAccumulation fmin fmax n q₁ ≤
      bidPriceP fmin fmax n q₂ * (q₂ - q₁) := by
  set a := n * rho (discountRatio fmin fmax)
  by_cases h2 : q₂ ≤ a
  · rw [V_below_eq fmin fmax n hfmin hf hn (le_trans hq₁ hq) h2,
      V_below_eq fmin fmax n hfmin hf hn hq₁ (le_trans hq h2)]
    have hP2_ge : fmin ≤ bidPriceP fmin fmax n q₂ :=
      (P_in_Icc_and_Q_eq fmin fmax n hfmin hf hn (le_trans hq₁ hq) hq₂).1.1
    nlinarith
  · push_neg at h2
    by_cases h1 : a ≤ q₁
    · exact V_diff_le_P_mul_above fmin fmax n hfmin hf hn h1 hq hq₂
    · push_neg at h1
      have ha0 : 0 ≤ a := mul_nonneg hn.le (rho_bounds fmin fmax hfmin hf).1.le
      have hpart1 : valueAccumulation fmin fmax n a - valueAccumulation fmin fmax n q₁ =
          fmin * (a - q₁) := by
        rw [V_below_eq fmin fmax n hfmin hf hn ha0 le_rfl,
          V_below_eq fmin fmax n hfmin hf hn hq₁ h1.le]
        ring
      have hpart2 : valueAccumulation fmin fmax n q₂ - valueAccumulation fmin fmax n a ≤
          bidPriceP fmin fmax n q₂ * (q₂ - a) :=
        V_diff_le_P_mul_above fmin fmax n hfmin hf hn le_rfl h2.le hq₂
      have hP2_ge : fmin ≤ bidPriceP fmin fmax n q₂ :=
        (P_in_Icc_and_Q_eq fmin fmax n hfmin hf hn (le_trans hq₁ hq) hq₂).1.1
      nlinarith

lemma V_diff_le_fare_mul (fmin fmax n : ℝ) (hfmin : 0 < fmin) (hf : fmin < fmax) (hn : 0 < n)
    {q₁ q₂ f : ℝ} (hf_mem : f ∈ Set.Icc fmin fmax)
    (hq₁ : 0 ≤ q₁) (hq : q₁ ≤ q₂) (hq₂ : q₂ ≤ protectionControl fmin fmax n f) :
    valueAccumulation fmin fmax n q₂ - valueAccumulation fmin fmax n q₁ ≤ f * (q₂ - q₁) := by
  have hQ_le_n : protectionControl fmin fmax n f ≤ n := (Q_bounds fmin fmax n hfmin hf hn hf_mem).2
  have hV := V_diff_le_P_mul fmin fmax n hfmin hf hn hq₁ hq (le_trans hq₂ hQ_le_n)
  have hP : bidPriceP fmin fmax n q₂ ≤ f :=
    (P_le_iff_le_Q fmin fmax n hfmin hf hn (le_trans hq₁ hq) (le_trans hq₂ hQ_le_n) hf_mem).mpr hq₂
  nlinarith

-- Section 2: General run properties and offlineOpt bounds
lemma runFrom_map_fst (P : DetPolicy) (n : ℝ) :
    ∀ (I : List Request) (hist : List (Request × ℝ)),
      (runFrom P n hist I).map Prod.fst = hist.map Prod.fst ++ I
  | [], hist => by simp [runFrom]
  | q :: qs, hist => by
    simp only [runFrom]
    rw [runFrom_map_fst P n qs]
    simp [List.map_append]

lemma run_map_fst (P : DetPolicy) (n : ℝ) (I : List Request) :
    (run P n I).map Prod.fst = I := by
  simpa [run] using runFrom_map_fst P n I []

lemma map_fst_comp (L : List (Request × ℝ)) (g : Request → ℝ) :
    L.map (fun e => g e.1) = (L.map Prod.fst).map g := by
  rw [List.map_map]
  rfl

lemma runFrom_inv (fmin fmax n : ℝ) (P : DetPolicy) :
    ∀ (I : List Request) (hist : List (Request × ℝ)),
      FaresIn (Set.Icc fmin fmax) I →
      (∀ e ∈ hist, e.1.fare ∈ Set.Icc fmin fmax ∧ 0 ≤ e.2 ∧ e.2 ≤ e.1.qty) →
      acceptedTotal hist ≤ n →
      (∀ e ∈ runFrom P n hist I, e.1.fare ∈ Set.Icc fmin fmax ∧ 0 ≤ e.2 ∧ e.2 ≤ e.1.qty) ∧
      acceptedTotal (runFrom P n hist I) ≤ n
  | [], hist, _, hhist, hsum => ⟨hhist, hsum⟩
  | q :: qs, hist, hI, hhist, hsum => by
    have hq_fare : q.fare ∈ Set.Icc fmin fmax := hI q List.mem_cons_self
    have hqs : FaresIn (Set.Icc fmin fmax) qs := fun r hr => hI r (List.mem_cons_of_mem _ hr)
    set a := max 0 (min (P.decide hist q) (min q.qty (n - acceptedTotal hist)))
    have ha0 : 0 ≤ a := le_max_left 0 _
    have ha_qty : a ≤ q.qty :=
      max_le q.qty_pos.le (le_trans (min_le_right _ _) (min_le_left _ _))
    have ha_cap : a ≤ n - acceptedTotal hist :=
      max_le (by linarith) (le_trans (min_le_right _ _) (min_le_right _ _))
    have hhist' : ∀ e ∈ hist ++ [(q, a)], e.1.fare ∈ Set.Icc fmin fmax ∧ 0 ≤ e.2 ∧ e.2 ≤ e.1.qty := by
      intro e he
      simp only [List.mem_append, List.mem_singleton] at he
      rcases he with he | rfl
      · exact hhist e he
      · exact ⟨hq_fare, ha0, ha_qty⟩
    have hsum' : acceptedTotal (hist ++ [(q, a)]) ≤ n := by
      unfold acceptedTotal at ha_cap hsum ⊢
      rw [List.map_append, List.sum_append]
      simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
      linarith
    exact runFrom_inv fmin fmax n P qs (hist ++ [(q, a)]) hqs hhist' hsum'

lemma sum_fin_eq_map_sum {α : Type*} (g : α → ℝ) :
    ∀ (I : List α), (∑ k : Fin I.length, g (I.get k)) = (I.map g).sum
  | [] => by simp
  | a :: as => by
    rw [List.map_cons, List.sum_cons, ← sum_fin_eq_map_sum g as]
    exact Fin.sum_univ_succ (fun k : Fin (as.length + 1) => g ((a :: as).get k))

lemma offlineOpt_nonempty (n : ℝ) (hn : 0 < n) (I : List Request) :
    {v : ℝ | ∃ x : Fin I.length → ℝ, IsFeasibleOffline n I x ∧
      v = ∑ i, (I.get i).fare * x i}.Nonempty := by
  refine ⟨0, fun _ => 0, ⟨⟨fun i => ⟨le_rfl, (I.get i).qty_pos.le⟩, by simp [hn.le]⟩, by simp⟩⟩

lemma offlineOpt_nonneg (n : ℝ) (hn : 0 < n) (I : List Request) :
    0 ≤ offlineOpt n I := by
  unfold offlineOpt
  have hbdd : BddAbove {v : ℝ | ∃ x : Fin I.length → ℝ, IsFeasibleOffline n I x ∧
      v = ∑ i, (I.get i).fare * x i} := by
    refine ⟨∑ i : Fin I.length, |(I.get i).fare| * (I.get i).qty, ?_⟩
    rintro v ⟨x, ⟨hx1, _⟩, rfl⟩
    refine Finset.sum_le_sum fun i _ => ?_
    calc (I.get i).fare * x i
        ≤ |(I.get i).fare * x i| := le_abs_self _
      _ = |(I.get i).fare| * |x i| := abs_mul _ _
      _ ≤ |(I.get i).fare| * (I.get i).qty := by
        rw [abs_of_nonneg (hx1 i).1]
        exact mul_le_mul_of_nonneg_left (hx1 i).2 (abs_nonneg _)
  exact le_csSup_of_le hbdd
    ⟨fun _ => 0, ⟨⟨fun i => ⟨le_rfl, (I.get i).qty_pos.le⟩, by simp [hn.le]⟩, by simp⟩⟩ le_rfl

lemma offlineOpt_le_full (fmin fmax n : ℝ) (hfmin : 0 < fmin) (hn : 0 < n)
    {I : List Request} (hI : FaresIn (Set.Icc fmin fmax) I) :
    offlineOpt n I ≤ (I.map fun q => q.fare * q.qty).sum := by
  unfold offlineOpt
  apply csSup_le (offlineOpt_nonempty n hn I)
  rintro v ⟨x, ⟨hx1, _⟩, rfl⟩
  rw [← sum_fin_eq_map_sum]
  refine Finset.sum_le_sum fun i _ => ?_
  have hfare : 0 < (I.get i).fare := lt_of_lt_of_le hfmin (hI (I.get i) (List.get_mem I i)).1
  exact mul_le_mul_of_nonneg_left (hx1 i).2 hfare.le

lemma offlineOpt_le_split (fmin fmax n : ℝ) (hfmin : 0 < fmin) (hn : 0 < n)
    {I : List Request} {f₀ : ℝ} (hf₀_mem : f₀ ∈ Set.Icc fmin fmax) :
    offlineOpt n I ≤
      f₀ * n + (I.map fun q => if f₀ < q.fare then (q.fare - f₀) * q.qty else 0).sum := by
  unfold offlineOpt
  have hf₀_pos : 0 < f₀ := lt_of_lt_of_le hfmin hf₀_mem.1
  apply csSup_le (offlineOpt_nonempty n hn I)
  rintro v ⟨x, ⟨hx1, hx2⟩, rfl⟩
  rw [← sum_fin_eq_map_sum]
  calc ∑ i : Fin I.length, (I.get i).fare * x i
      ≤ ∑ i : Fin I.length,
          (f₀ * x i + (if f₀ < (I.get i).fare then ((I.get i).fare - f₀) * (I.get i).qty else 0)) := by
        refine Finset.sum_le_sum fun i _ => ?_
        split_ifs with hgt
        · have hmul : ((I.get i).fare - f₀) * x i ≤ ((I.get i).fare - f₀) * (I.get i).qty :=
            mul_le_mul_of_nonneg_left (hx1 i).2 (by linarith)
          linarith
        · have hmul : (I.get i).fare * x i ≤ f₀ * x i :=
            mul_le_mul_of_nonneg_right (not_lt.mp hgt) (hx1 i).1
          linarith
    _ = f₀ * (∑ i : Fin I.length, x i) +
          ∑ i : Fin I.length, (if f₀ < (I.get i).fare then ((I.get i).fare - f₀) * (I.get i).qty else 0) := by
        rw [Finset.sum_add_distrib, ← Finset.mul_sum]
    _ ≤ f₀ * n +
          ∑ i : Fin I.length, (if f₀ < (I.get i).fare then ((I.get i).fare - f₀) * (I.get i).qty else 0) := by
        linarith [mul_le_mul_of_nonneg_left hx2 hf₀_pos.le]

lemma sum_diff_le_sum_full (fmin fmax : ℝ) (hfmin : 0 < fmin)
    {f₀ : ℝ} (hf₀_mem : f₀ ∈ Set.Icc fmin fmax) :
    ∀ (I : List Request),
      (I.map fun q => if f₀ < q.fare then (q.fare - f₀) * q.qty else 0).sum ≤
        (I.map fun q => if f₀ < q.fare then q.fare * q.qty else 0).sum
  | [] => by simp
  | q :: qs => by
    have ih := sum_diff_le_sum_full fmin fmax hfmin hf₀_mem qs
    have hf₀_pos : 0 < f₀ := lt_of_lt_of_le hfmin hf₀_mem.1
    simp only [List.map_cons, List.sum_cons]
    split_ifs with hgt
    · have : (q.fare - f₀) * q.qty ≤ q.fare * q.qty := by nlinarith [q.qty_pos]
      linarith
    · linarith

-- Extraction of maximum rejected fare
lemma all_full_or_max_rejected (fmin fmax : ℝ) (L : List (Request × ℝ))
    (hL : ∀ e ∈ L, e.1.fare ∈ Set.Icc fmin fmax ∧ 0 ≤ e.2 ∧ e.2 ≤ e.1.qty) :
    (∀ e ∈ L, e.2 = e.1.qty) ∨
      ∃ f' ∈ Set.Icc fmin fmax,
        (∃ e₀ ∈ L, e₀.1.fare = f' ∧ e₀.2 < e₀.1.qty) ∧
        (∀ e ∈ L, f' < e.1.fare → e.2 = e.1.qty) := by
  classical
  set S := ((L.filter fun e => decide (e.2 < e.1.qty)).map fun e => e.1.fare).toFinset
  by_cases hS : S.Nonempty
  · right
    let f' := S.max' hS
    have hf'_mem : f' ∈ S := Finset.max'_mem S hS
    simp only [S, List.mem_toFinset, List.mem_map, List.mem_filter, decide_eq_true_eq] at hf'_mem
    rcases hf'_mem with ⟨e₀, ⟨he₀_mem, he₀_lt⟩, he₀_fare⟩
    have he₀_bds := hL e₀ he₀_mem
    refine ⟨f', he₀_fare ▸ he₀_bds.1, ⟨e₀, he₀_mem, he₀_fare, he₀_lt⟩, ?_⟩
    intro e he hgt
    have he_le := (hL e he).2.2
    rcases he_le.lt_or_eq with hlt_qty | heq
    · exfalso
      have hmem : e.1.fare ∈ S := by
        simp only [S, List.mem_toFinset, List.mem_map, List.mem_filter, decide_eq_true_eq]
        exact ⟨e, ⟨he, hlt_qty⟩, rfl⟩
      have hmax : e.1.fare ≤ f' := Finset.le_max' S e.1.fare hmem
      linarith
    · exact heq
  · left
    rw [Finset.not_nonempty_iff_eq_empty] at hS
    intro e he
    have he_le := (hL e he).2.2
    rcases he_le.lt_or_eq with hlt_qty | heq
    · exfalso
      have hmem : e.1.fare ∈ S := by
        simp only [S, List.mem_toFinset, List.mem_map, List.mem_filter, decide_eq_true_eq]
        exact ⟨e, ⟨he, hlt_qty⟩, rfl⟩
      rw [hS] at hmem
      exact Finset.notMem_empty _ hmem
    · exact heq

-- Section 3: Order Quantity Policy (`orderQuantityPolicy`)
lemma orderQuantityPolicy_step (fmin fmax n : ℝ) (hfmin : 0 < fmin) (hf : fmin < fmax) (hn : 0 < n)
    (hist : List (Request × ℝ)) (q : Request)
    (hq0 : 0 ≤ acceptedTotal hist) (hqn : acceptedTotal hist ≤ n)
    (hq_fare : q.fare ∈ Set.Icc fmin fmax) :
    let P_pol := orderQuantityPolicy fmin fmax n (protectionControl fmin fmax n)
    max 0 (min (P_pol.decide hist q) (min q.qty (n - acceptedTotal hist))) =
      max 0 (min q.qty (protectionControl fmin fmax n q.fare - acceptedTotal hist)) := by
  intro P_pol
  set qhat := acceptedTotal hist
  set Q := protectionControl fmin fmax n
  have hQ_le_n : Q q.fare ≤ n := (Q_bounds fmin fmax n hfmin hf hn hq_fare).2
  by_cases hq_le : qhat ≤ Q q.fare
  · have hprice : orderQuantityControl fmin fmax Q qhat ≤ q.fare :=
      (P_le_iff_le_Q fmin fmax n hfmin hf hn hq0 hqn hq_fare).mpr hq_le
    have hnot_lt : ¬ (q.fare < orderQuantityControl fmin fmax Q qhat) := not_lt.mpr hprice
    have hM0 : 0 ≤ min q.qty (Q q.fare - qhat) := le_min q.qty_pos.le (by linarith)
    have hsup : P_pol.decide hist q = min q.qty (Q q.fare - qhat) := by
      dsimp [P_pol, orderQuantityPolicy]
      rw [if_neg hnot_lt]
      apply IsGreatest.csSup_eq
      constructor
      · refine ⟨hM0, min_le_left _ _, ?_, ?_⟩
        · have : min q.qty (Q q.fare - qhat) ≤ Q q.fare - qhat := min_le_right _ _
          linarith
        · have hle_Q : min q.qty (Q q.fare - qhat) + qhat ≤ Q q.fare := by
            have : min q.qty (Q q.fare - qhat) ≤ Q q.fare - qhat := min_le_right _ _
            linarith
          exact (P_le_iff_le_Q fmin fmax n hfmin hf hn (by linarith) (by linarith) hq_fare).mpr hle_Q
      · rintro α ⟨hα0, hα_qty, hα_n, hα_price⟩
        have hle_Q := (P_le_iff_le_Q fmin fmax n hfmin hf hn (by linarith) hα_n hq_fare).mp hα_price
        exact le_min hα_qty (by linarith)
    rw [hsup]
    have hmin2 :
        min (min q.qty (Q q.fare - qhat)) (min q.qty (n - qhat)) =
          min q.qty (Q q.fare - qhat) := by
      apply min_eq_left
      exact min_le_min le_rfl (by linarith)
    rw [hmin2]
  · have hprice : q.fare < orderQuantityControl fmin fmax Q qhat := by
      by_contra hge
      have hle := (P_le_iff_le_Q fmin fmax n hfmin hf hn hq0 hqn hq_fare).mp (not_lt.mp hge)
      exact hq_le hle
    have hpol0 : P_pol.decide hist q = 0 := by
      dsimp [P_pol, orderQuantityPolicy]
      rw [if_pos hprice]
    rw [hpol0]
    have h1 : min (0 : ℝ) (min q.qty (n - qhat)) = 0 :=
      min_eq_left (le_min q.qty_pos.le (by linarith))
    have h2 : max 0 (min q.qty (Q q.fare - qhat)) = 0 :=
      max_eq_left (le_trans (min_le_right _ _) (by linarith))
    rw [h1, max_self, h2]

lemma V_clamp_step_bound (fmin fmax n : ℝ) (hfmin : 0 < fmin) (hf : fmin < fmax) (hn : 0 < n)
    {f' : ℝ} (hf'_mem : f' ∈ Set.Icc fmin fmax)
    {c : ℝ} (hc_mem : c ∈ Set.Icc fmin fmax)
    {q y : ℝ} (hq0 : 0 ≤ q) (hy0 : 0 ≤ y)
    (hy_Q : 0 < y → q + y ≤ protectionControl fmin fmax n c) :
    let Qf' := protectionControl fmin fmax n f'
    valueAccumulation fmin fmax n (min (q + y) Qf') -
      valueAccumulation fmin fmax n (min q Qf') +
      (if f' < c then (c - f') * y else 0) ≤ c * y := by
  intro Qf'
  rcases hy0.eq_or_lt with rfl | hy_pos
  · simp
  · have hq_le : q + y ≤ protectionControl fmin fmax n c := hy_Q hy_pos
    have hQf'_nonneg : 0 ≤ Qf' := Q_nonneg fmin fmax n hfmin hf hn hf'_mem
    have hmin1_0 : 0 ≤ min q Qf' := le_min hq0 hQf'_nonneg
    have hmin_mono : min q Qf' ≤ min (q + y) Qf' := min_le_min (by linarith) le_rfl
    have hmin_diff : min (q + y) Qf' - min q Qf' ≤ y := by
      rcases le_total (q + y) Qf' with h1 | h1 <;>
      rcases le_total q Qf' with h2 | h2 <;>
      simp only [min_eq_left, min_eq_right, *] <;> linarith
    split_ifs with hgt
    · have hV := V_diff_le_fare_mul fmin fmax n hfmin hf hn hf'_mem hmin1_0 hmin_mono (min_le_right _ _)
      have hf'_pos : 0 < f' := lt_of_lt_of_le hfmin hf'_mem.1
      nlinarith
    · have hc_le_f' : c ≤ f' := not_lt.mp hgt
      have hc_pos : 0 < c := lt_of_lt_of_le hfmin hc_mem.1
      have hf'_pos : 0 < f' := lt_of_lt_of_le hfmin hf'_mem.1
      have hQc_le_Qf' : protectionControl fmin fmax n c ≤ Qf' :=
        (Q_le_iff fmin fmax n hfmin hf hn hc_pos hf'_pos).mpr hc_le_f'
      have hmin2_le : min (q + y) Qf' ≤ protectionControl fmin fmax n c :=
        le_trans (min_le_left _ _) hq_le
      have hV := V_diff_le_fare_mul fmin fmax n hfmin hf hn hc_mem hmin1_0 hmin_mono hmin2_le
      nlinarith

lemma runFrom_orderQuantity_props (fmin fmax n : ℝ) (hfmin : 0 < fmin) (hf : fmin < fmax) (hn : 0 < n)
    {f' : ℝ} (hf'_mem : f' ∈ Set.Icc fmin fmax) :
    ∀ (I : List Request) (hist : List (Request × ℝ)),
      FaresIn (Set.Icc fmin fmax) I →
      (∀ e ∈ hist, e.1.fare ∈ Set.Icc fmin fmax ∧ 0 ≤ e.2 ∧ e.2 ≤ e.1.qty) →
      acceptedTotal hist ≤ n →
      let P_pol := orderQuantityPolicy fmin fmax n (protectionControl fmin fmax n)
      let final := runFrom P_pol n hist I
      let Qf' := protectionControl fmin fmax n f'
      acceptedTotal hist ≤ acceptedTotal final ∧
      (∀ e ∈ final, e.2 < e.1.qty → e ∈ hist ∨ protectionControl fmin fmax n e.1.fare ≤ acceptedTotal final) ∧
      valueAccumulation fmin fmax n (min (acceptedTotal final) Qf') +
        (final.map fun e => if f' < e.1.fare then (e.1.fare - f') * e.2 else 0).sum -
        (valueAccumulation fmin fmax n (min (acceptedTotal hist) Qf') +
          (hist.map fun e => if f' < e.1.fare then (e.1.fare - f') * e.2 else 0).sum) ≤
        (final.map fun e => e.1.fare * e.2).sum - (hist.map fun e => e.1.fare * e.2).sum
  | [], hist, _, _, _ => by
    simp only [runFrom]
    refine ⟨le_rfl, fun e he _ => Or.inl he, by linarith⟩
  | q :: qs, hist, hI, hhist, hsum => by
    simp only [runFrom]
    have hq_fare : q.fare ∈ Set.Icc fmin fmax := hI q List.mem_cons_self
    have hqs : FaresIn (Set.Icc fmin fmax) qs := fun r hr => hI r (List.mem_cons_of_mem _ hr)
    set P_pol := orderQuantityPolicy fmin fmax n (protectionControl fmin fmax n)
    set qhat := acceptedTotal hist
    have hq0 : 0 ≤ qhat :=
      List.sum_nonneg (by intro x hx; rw [List.mem_map] at hx; rcases hx with ⟨e, he, rfl⟩; exact (hhist e he).2.1)
    have hy_eq := orderQuantityPolicy_step fmin fmax n hfmin hf hn hist q hq0 hsum hq_fare
    set y := max 0 (min (P_pol.decide hist q) (min q.qty (n - qhat)))
    have hy0 : 0 ≤ y := le_max_left 0 _
    have hy_qty : y ≤ q.qty := by
      have hy_eq' : y = max 0 (min q.qty (protectionControl fmin fmax n q.fare - qhat)) := hy_eq
      rw [hy_eq']
      exact max_le q.qty_pos.le (min_le_left _ _)
    have hQq_le_n : protectionControl fmin fmax n q.fare ≤ n :=
      (Q_bounds fmin fmax n hfmin hf hn hq_fare).2
    have hy_Q : 0 < y → qhat + y ≤ protectionControl fmin fmax n q.fare := by
      intro hy_pos
      have hy_eq' : y = max 0 (min q.qty (protectionControl fmin fmax n q.fare - qhat)) := hy_eq
      rw [hy_eq'] at hy_pos ⊢
      have hmin_pos : 0 < min q.qty (protectionControl fmin fmax n q.fare - qhat) := by
        by_contra hle
        rw [max_eq_left (not_lt.mp hle)] at hy_pos
        exact lt_irrefl 0 hy_pos
      rw [max_eq_right hmin_pos.le]
      have : min q.qty (protectionControl fmin fmax n q.fare - qhat) ≤
          protectionControl fmin fmax n q.fare - qhat := min_le_right _ _
      linarith
    have hhist' : ∀ e ∈ hist ++ [(q, y)], e.1.fare ∈ Set.Icc fmin fmax ∧ 0 ≤ e.2 ∧ e.2 ≤ e.1.qty := by
      intro e he
      simp only [List.mem_append, List.mem_singleton] at he
      rcases he with he | rfl
      · exact hhist e he
      · exact ⟨hq_fare, hy0, hy_qty⟩
    have hsum_step : acceptedTotal (hist ++ [(q, y)]) = qhat + y := by
      unfold acceptedTotal
      rw [List.map_append, List.sum_append]
      simp [qhat, acceptedTotal]
    have hsum' : acceptedTotal (hist ++ [(q, y)]) ≤ n := by
      rw [hsum_step]
      rcases hy0.eq_or_lt with h0 | hpos
      · linarith
      · linarith [hy_Q hpos]
    obtain ⟨ih_mono, ih_rej, ih_V⟩ :=
      runFrom_orderQuantity_props fmin fmax n hfmin hf hn hf'_mem qs (hist ++ [(q, y)]) hqs hhist' hsum'
    refine ⟨?_, ?_, ?_⟩
    · linarith [hsum_step, ih_mono]
    · intro e he hlt
      rcases ih_rej e he hlt with he_in | hge
      · simp only [List.mem_append, List.mem_singleton] at he_in
        rcases he_in with he_in | rfl
        · exact Or.inl he_in
        · right
          change y < q.qty at hlt
          have hy_eq' : y = max 0 (min q.qty (protectionControl fmin fmax n q.fare - qhat)) := hy_eq
          have hq_ge : protectionControl fmin fmax n q.fare ≤ qhat + y := by
            rw [hy_eq'] at hlt ⊢
            have hmin_lt : min q.qty (protectionControl fmin fmax n q.fare - qhat) < q.qty :=
              lt_of_le_of_lt (le_max_right _ _) hlt
            have hmin_eq : min q.qty (protectionControl fmin fmax n q.fare - qhat) =
                protectionControl fmin fmax n q.fare - qhat :=
              min_eq_right (le_of_not_ge fun hge => hmin_lt.not_ge (min_eq_left hge).ge)
            have : protectionControl fmin fmax n q.fare - qhat ≤
                max 0 (min q.qty (protectionControl fmin fmax n q.fare - qhat)) := by
              rw [hmin_eq]; exact le_max_right _ _
            linarith
          change protectionControl fmin fmax n q.fare ≤ _
          linarith [hsum_step, ih_mono]
      · exact Or.inr hge
    · have hV_step := V_clamp_step_bound fmin fmax n hfmin hf hn hf'_mem hq_fare hq0 hy0 hy_Q
      have hmap1 :
          ((hist ++ [(q, y)]).map fun e => if f' < e.1.fare then (e.1.fare - f') * e.2 else 0).sum =
            (hist.map fun e => if f' < e.1.fare then (e.1.fare - f') * e.2 else 0).sum +
              (if f' < q.fare then (q.fare - f') * y else 0) := by
        rw [List.map_append, List.sum_append]
        simp
      have hmap2 :
          ((hist ++ [(q, y)]).map fun e => e.1.fare * e.2).sum =
            (hist.map fun e => e.1.fare * e.2).sum + q.fare * y := by
        rw [List.map_append, List.sum_append]
        simp
      rw [hsum_step, hmap1, hmap2] at ih_V
      linarith

lemma orderQuantity_instance_bound (fmin fmax n : ℝ) (hfmin : 0 < fmin) (hf : fmin < fmax)
    (hn : 0 < n) (I : List Request) (hI : FaresIn (Set.Icc fmin fmax) I) :
    1 / (1 - Real.log (discountRatio fmin fmax)) * offlineOpt n I ≤
      revenue n (orderQuantityPolicy fmin fmax n (protectionControl fmin fmax n)) I := by
  obtain ⟨hρ_pos, hρ_lt1⟩ := rho_bounds fmin fmax hfmin hf
  change rho (discountRatio fmin fmax) * offlineOpt n I ≤ _
  set P_pol := orderQuantityPolicy fmin fmax n (protectionControl fmin fmax n)
  set L := run P_pol n I
  have hL_inv : (∀ e ∈ L, e.1.fare ∈ Set.Icc fmin fmax ∧ 0 ≤ e.2 ∧ e.2 ≤ e.1.qty) ∧
      acceptedTotal L ≤ n :=
    runFrom_inv fmin fmax n P_pol I [] hI (by simp) (by simp [acceptedTotal, hn.le])
  rcases all_full_or_max_rejected fmin fmax L hL_inv.1 with hfull | ⟨f', hf'_mem, ⟨e₀, he₀_mem, he₀_fare, he₀_lt⟩, hfull_gt⟩
  · -- Case 1: all requests accepted in full
    have hrev_eq : revenue n P_pol I = (I.map fun q => q.fare * q.qty).sum := by
      unfold revenue
      have hcongr : L.map (fun e => e.1.fare * e.2) = L.map (fun e => e.1.fare * e.1.qty) := by
        apply List.map_congr_left
        intro e he
        rw [hfull e he]
      rw [hcongr, map_fst_comp L (fun q => q.fare * q.qty), run_map_fst]
    have hopt_le := offlineOpt_le_full fmin fmax n hfmin hn hI
    have hopt_nonneg := offlineOpt_nonneg n hn I
    calc rho (discountRatio fmin fmax) * offlineOpt n I
        ≤ 1 * offlineOpt n I := mul_le_mul_of_nonneg_right hρ_lt1.le hopt_nonneg
      _ = offlineOpt n I := one_mul _
      _ ≤ (I.map fun q => q.fare * q.qty).sum := hopt_le
      _ = revenue n P_pol I := hrev_eq.symm
  · -- Case 2: some request of fare f' not accepted in full
    obtain ⟨_, hL_rej, hL_V⟩ :=
      runFrom_orderQuantity_props fmin fmax n hfmin hf hn hf'_mem I [] hI (by simp) (by simp [acceptedTotal, hn.le])
    rcases hL_rej e₀ he₀_mem he₀_lt with he₀_nil | hq_ge
    · simp at he₀_nil
    · rw [he₀_fare] at hq_ge
      set Qf' := protectionControl fmin fmax n f'
      change valueAccumulation fmin fmax n (min (acceptedTotal L) Qf') +
          (L.map fun e => if f' < e.1.fare then (e.1.fare - f') * e.2 else 0).sum -
          (valueAccumulation fmin fmax n (min (acceptedTotal ([] : List (Request × ℝ))) Qf') +
          (([] : List (Request × ℝ)).map fun e => if f' < e.1.fare then (e.1.fare - f') * e.2 else 0).sum) ≤
        (L.map fun e => e.1.fare * e.2).sum - (([] : List (Request × ℝ)).map fun e => e.1.fare * e.2).sum at hL_V
      have hmin_final : min (acceptedTotal L) Qf' = Qf' := min_eq_right hq_ge
      have hmin_init : min (acceptedTotal ([] : List (Request × ℝ))) Qf' = 0 := by
        have h0 : acceptedTotal ([] : List (Request × ℝ)) = 0 := by simp [acceptedTotal]
        rw [h0]
        exact min_eq_left (Q_nonneg fmin fmax n hfmin hf hn hf'_mem)
      have hV_final : valueAccumulation fmin fmax n Qf' =
          rho (discountRatio fmin fmax) * (f' * n) := V_Q_eq fmin fmax n hfmin hf hn hf'_mem
      rw [hmin_final, hmin_init, V_zero] at hL_V
      simp only [List.map_nil, List.sum_nil, add_zero, sub_zero] at hL_V
      have hhead_eq :
          (L.map fun e => if f' < e.1.fare then (e.1.fare - f') * e.2 else 0).sum =
            (I.map fun q => if f' < q.fare then (q.fare - f') * q.qty else 0).sum := by
        have hcongr :
            L.map (fun e => if f' < e.1.fare then (e.1.fare - f') * e.2 else 0) =
              L.map (fun e => if f' < e.1.fare then (e.1.fare - f') * e.1.qty else 0) := by
          apply List.map_congr_left
          intro e he
          split_ifs with hgt
          · rw [hfull_gt e he hgt]
          · rfl
        rw [hcongr, map_fst_comp L (fun q => if f' < q.fare then (q.fare - f') * q.qty else 0),
          run_map_fst]
      have hdiff_nonneg :
          0 ≤ (I.map fun q => if f' < q.fare then (q.fare - f') * q.qty else 0).sum := by
        apply List.sum_nonneg
        intro x hx
        rw [List.mem_map] at hx
        rcases hx with ⟨q, _, rfl⟩
        split_ifs with hgt
        · exact mul_nonneg (by linarith) q.qty_pos.le
        · exact le_rfl
      have hopt_le := offlineOpt_le_split fmin fmax n hfmin hn hf'_mem (I := I)
      unfold revenue
      set S_diff := (I.map fun q => if f' < q.fare then (q.fare - f') * q.qty else 0).sum
      calc rho (discountRatio fmin fmax) * offlineOpt n I
          ≤ rho (discountRatio fmin fmax) * (f' * n + S_diff) :=
            mul_le_mul_of_nonneg_left hopt_le hρ_pos.le
        _ = rho (discountRatio fmin fmax) * (f' * n) + rho (discountRatio fmin fmax) * S_diff := by ring
        _ ≤ rho (discountRatio fmin fmax) * (f' * n) + 1 * S_diff := by
            linarith [mul_le_mul_of_nonneg_right hρ_lt1.le hdiff_nonneg]
        _ = valueAccumulation fmin fmax n Qf' +
              (L.map fun e => if f' < e.1.fare then (e.1.fare - f') * e.2 else 0).sum := by
            rw [one_mul, hV_final, hhead_eq]
        _ ≤ (L.map fun e => e.1.fare * e.2).sum := hL_V

-- Section 4: Protection-Level Policy (`protectionLevelPolicy`)
lemma acceptedAtOrBelow_append_singleton (f : ℝ) (hist : List (Request × ℝ)) (q : Request) (y : ℝ) :
    acceptedAtOrBelow f (hist ++ [(q, y)]) =
      acceptedAtOrBelow f hist + (if q.fare ≤ f then y else 0) := by
  unfold acceptedAtOrBelow
  rw [List.filter_append]
  by_cases h : q.fare ≤ f <;> simp [h]

lemma acceptedAtOrBelow_fmax (fmax : ℝ) (hist : List (Request × ℝ))
    (h : ∀ e ∈ hist, e.1.fare ≤ fmax) :
    acceptedAtOrBelow fmax hist = acceptedTotal hist := by
  unfold acceptedAtOrBelow acceptedTotal
  have hfilt : hist.filter (fun e => decide (e.1.fare ≤ fmax)) = hist := by
    rw [List.filter_eq_self]
    intro e he
    simp [h e he]
  rw [hfilt]

noncomputable def candFares (f_low fmax : ℝ) (hist : List (Request × ℝ)) : Finset ℝ :=
  insert f_low ((hist.map fun e => e.1.fare).toFinset.filter fun g => f_low ≤ g ∧ g ≤ fmax)

lemma mem_candFares_self (f_low fmax : ℝ) (hist : List (Request × ℝ)) :
    f_low ∈ candFares f_low fmax hist :=
  Finset.mem_insert_self _ _

lemma candFares_subset_Icc (f_low fmax : ℝ) (hf_low : f_low ≤ fmax) (hist : List (Request × ℝ))
    {g : ℝ} (hg : g ∈ candFares f_low fmax hist) : g ∈ Set.Icc f_low fmax := by
  unfold candFares at hg
  rw [Finset.mem_insert, Finset.mem_filter] at hg
  rcases hg with rfl | ⟨_, h1, h2⟩
  · exact ⟨le_rfl, hf_low⟩
  · exact ⟨h1, h2⟩

lemma candFares_step_reduction (fmin fmax n : ℝ) (hfmin : 0 < fmin) (hf : fmin < fmax) (hn : 0 < n)
    (hist : List (Request × ℝ))
    {f_low : ℝ} (hf_low_mem : f_low ∈ Set.Icc fmin fmax)
    {f : ℝ} (hf_mem : f ∈ Set.Icc f_low fmax) :
    ∃ g ∈ candFares f_low fmax hist,
      g ≤ f ∧
      protectionControl fmin fmax n g - acceptedAtOrBelow g hist ≤
        protectionControl fmin fmax n f - acceptedAtOrBelow f hist := by
  classical
  set S_le := (candFares f_low fmax hist).filter fun g => g ≤ f
  have hf_low_in : f_low ∈ S_le := by
    simp only [S_le, Finset.mem_filter]
    exact ⟨mem_candFares_self f_low fmax hist, hf_mem.1⟩
  have hS_ne : S_le.Nonempty := ⟨f_low, hf_low_in⟩
  let g := S_le.max' hS_ne
  have hg_in : g ∈ S_le := Finset.max'_mem S_le hS_ne
  rw [Finset.mem_filter] at hg_in
  obtain ⟨hg_cand, hg_le_f⟩ := hg_in
  have hg_Icc := candFares_subset_Icc f_low fmax hf_low_mem.2 hist hg_cand
  have hf_low_le_g : f_low ≤ g := hg_Icc.1
  have heq_acc : acceptedAtOrBelow g hist = acceptedAtOrBelow f hist := by
    unfold acceptedAtOrBelow
    congr 2
    apply List.filter_congr
    intro e he
    simp only [decide_eq_decide]
    constructor
    · intro hle
      exact le_trans hle hg_le_f
    · intro hle
      by_cases hlt : e.1.fare < f_low
      · exact le_trans hlt.le hf_low_le_g
      · push_neg at hlt
        have he_cand : e.1.fare ∈ candFares f_low fmax hist := by
          unfold candFares
          rw [Finset.mem_insert]
          right
          rw [Finset.mem_filter, List.mem_toFinset, List.mem_map]
          exact ⟨⟨e, he, rfl⟩, hlt, le_trans hle hf_mem.2⟩
        have he_S : e.1.fare ∈ S_le := Finset.mem_filter.mpr ⟨he_cand, hle⟩
        exact Finset.le_max' S_le e.1.fare he_S
  have hg_pos : 0 < g := lt_of_lt_of_le hfmin (le_trans hf_low_mem.1 hf_low_le_g)
  have hf_pos : 0 < f := lt_of_lt_of_le hfmin (le_trans hf_low_mem.1 hf_mem.1)
  have hQ_le : protectionControl fmin fmax n g ≤ protectionControl fmin fmax n f :=
    (Q_le_iff fmin fmax n hfmin hf hn hg_pos hf_pos).mpr hg_le_f
  exact ⟨g, hg_cand, hg_le_f, by linarith⟩

lemma protectionLevelPolicy_step (fmin fmax n : ℝ) (hfmin : 0 < fmin) (hf : fmin < fmax) (hn : 0 < n)
    (hist : List (Request × ℝ)) (q : Request)
    (hhist_max : ∀ e ∈ hist, e.1.fare ≤ fmax)
    (hq_fare : q.fare ∈ Set.Icc fmin fmax)
    (hQ : ∀ f ∈ Set.Icc fmin fmax, acceptedAtOrBelow f hist ≤ protectionControl fmin fmax n f) :
    let P_pol := protectionLevelPolicy fmax (protectionControl fmin fmax n)
    let M := (candFares q.fare fmax hist).inf' ⟨q.fare, mem_candFares_self q.fare fmax hist⟩
      (fun g => protectionControl fmin fmax n g - acceptedAtOrBelow g hist)
    max 0 (min (P_pol.decide hist q) (min q.qty (n - acceptedTotal hist))) = min q.qty M ∧
    0 ≤ min q.qty M ∧
    ∀ f ∈ Set.Icc q.fare fmax, M ≤ protectionControl fmin fmax n f - acceptedAtOrBelow f hist := by
  intro P_pol M
  have hM_le_all : ∀ f ∈ Set.Icc q.fare fmax,
      M ≤ protectionControl fmin fmax n f - acceptedAtOrBelow f hist := by
    intro f hf_mem
    obtain ⟨g, hg_cand, _, hle⟩ := candFares_step_reduction fmin fmax n hfmin hf hn hist hq_fare hf_mem
    exact le_trans (Finset.inf'_le _ hg_cand) hle
  have hM_nonneg : 0 ≤ M := by
    refine (Finset.le_inf'_iff _ _).mpr fun g hg => ?_
    have hg_Icc := candFares_subset_Icc q.fare fmax hq_fare.2 hist hg
    have hg_mem : g ∈ Set.Icc fmin fmax := ⟨le_trans hq_fare.1 hg_Icc.1, hg_Icc.2⟩
    linarith [hQ g hg_mem]
  have hmin_nonneg : 0 ≤ min q.qty M := le_min q.qty_pos.le hM_nonneg
  have hsup : P_pol.decide hist q = min q.qty M := by
    dsimp [P_pol, protectionLevelPolicy]
    apply IsGreatest.csSup_eq
    constructor
    · refine ⟨hmin_nonneg, min_le_left _ _, fun f hf_mem => ?_⟩
      have h1 : min q.qty M ≤ M := min_le_right _ _
      have h2 := hM_le_all f hf_mem
      linarith
    · rintro α ⟨_, hα_qty, hα_Q⟩
      refine le_min hα_qty ?_
      refine (Finset.le_inf'_iff _ _).mpr fun g hg => ?_
      have hg_Icc := candFares_subset_Icc q.fare fmax hq_fare.2 hist hg
      linarith [hα_Q g hg_Icc]
  have hfmax_mem : fmax ∈ Set.Icc q.fare fmax := ⟨hq_fare.2, le_rfl⟩
  have hM_le_cap : M ≤ n - acceptedTotal hist := by
    calc M ≤ protectionControl fmin fmax n fmax - acceptedAtOrBelow fmax hist := hM_le_all fmax hfmax_mem
      _ = n - acceptedTotal hist := by
        rw [Q_fmax fmin fmax n hfmin hf, acceptedAtOrBelow_fmax fmax hist hhist_max]
  refine ⟨?_, hmin_nonneg, hM_le_all⟩
  rw [hsup]
  have hmin2 : min (min q.qty M) (min q.qty (n - acceptedTotal hist)) = min q.qty M := by
    apply min_eq_left
    exact min_le_min le_rfl hM_le_cap
  rw [hmin2, max_eq_right hmin_nonneg]

lemma runFrom_protection_props (fmin fmax n : ℝ) (hfmin : 0 < fmin) (hf : fmin < fmax) (hn : 0 < n) :
    ∀ (I : List Request) (hist : List (Request × ℝ)),
      FaresIn (Set.Icc fmin fmax) I →
      (∀ e ∈ hist, e.1.fare ∈ Set.Icc fmin fmax ∧ 0 ≤ e.2 ∧ e.2 ≤ e.1.qty) →
      (∀ f ∈ Set.Icc fmin fmax, acceptedAtOrBelow f hist ≤ protectionControl fmin fmax n f) →
      let P_pol := protectionLevelPolicy fmax (protectionControl fmin fmax n)
      let final := runFrom P_pol n hist I
      (∀ f ∈ Set.Icc fmin fmax, acceptedAtOrBelow f hist ≤ acceptedAtOrBelow f final ∧
        acceptedAtOrBelow f final ≤ protectionControl fmin fmax n f) ∧
      (∀ e ∈ final, e.2 < e.1.qty →
        e ∈ hist ∨ ∃ f₀ ∈ Set.Icc e.1.fare fmax,
          acceptedAtOrBelow f₀ final = protectionControl fmin fmax n f₀)
  | [], hist, _, _, hQ => by
    simp only [runFrom]
    exact ⟨fun f hf_mem => ⟨le_rfl, hQ f hf_mem⟩, fun e he _ => Or.inl he⟩
  | q :: qs, hist, hI, hhist, hQ => by
    simp only [runFrom]
    have hq_fare : q.fare ∈ Set.Icc fmin fmax := hI q List.mem_cons_self
    have hqs : FaresIn (Set.Icc fmin fmax) qs := fun r hr => hI r (List.mem_cons_of_mem _ hr)
    have hhist_max : ∀ e ∈ hist, e.1.fare ≤ fmax := fun e he => (hhist e he).1.2
    obtain ⟨hy_eq, hy0, hM_le_all⟩ := protectionLevelPolicy_step fmin fmax n hfmin hf hn hist q hhist_max hq_fare hQ
    set P_pol := protectionLevelPolicy fmax (protectionControl fmin fmax n)
    set M := (candFares q.fare fmax hist).inf' ⟨q.fare, mem_candFares_self q.fare fmax hist⟩
      (fun g => protectionControl fmin fmax n g - acceptedAtOrBelow g hist)
    set y := max 0 (min (P_pol.decide hist q) (min q.qty (n - acceptedTotal hist)))
    have hy_qty : y ≤ q.qty := hy_eq ▸ min_le_left _ _
    have hhist' : ∀ e ∈ hist ++ [(q, y)], e.1.fare ∈ Set.Icc fmin fmax ∧ 0 ≤ e.2 ∧ e.2 ≤ e.1.qty := by
      intro e he
      simp only [List.mem_append, List.mem_singleton] at he
      rcases he with he | rfl
      · exact hhist e he
      · exact ⟨hq_fare, hy_eq ▸ hy0, hy_qty⟩
    have hQ' : ∀ f ∈ Set.Icc fmin fmax, acceptedAtOrBelow f (hist ++ [(q, y)]) ≤ protectionControl fmin fmax n f := by
      intro f hf_mem
      rw [acceptedAtOrBelow_append_singleton]
      split_ifs with hle
      · have hf_Icc : f ∈ Set.Icc q.fare fmax := ⟨hle, hf_mem.2⟩
        have hM_le := hM_le_all f hf_Icc
        have hy_le_M : y ≤ M := hy_eq ▸ min_le_right _ _
        linarith
      · linarith [hQ f hf_mem]
    obtain ⟨ih_Q, ih_e⟩ := runFrom_protection_props fmin fmax n hfmin hf hn qs (hist ++ [(q, y)]) hqs hhist' hQ'
    refine ⟨fun f hf_mem => ?_, fun e he hlt => ?_⟩
    · obtain ⟨h1, h2⟩ := ih_Q f hf_mem
      have hstep : acceptedAtOrBelow f hist ≤ acceptedAtOrBelow f (hist ++ [(q, y)]) := by
        rw [acceptedAtOrBelow_append_singleton]
        have hy_nonneg : 0 ≤ y := hy_eq ▸ hy0
        split_ifs <;> linarith
      exact ⟨le_trans hstep h1, h2⟩
    · rcases ih_e e he hlt with he_in | htight
      · simp only [List.mem_append, List.mem_singleton] at he_in
        rcases he_in with he_in | rfl
        · exact Or.inl he_in
        · right
          change y < q.qty at hlt
          have hy_eq_M : y = M := by
            rw [hy_eq] at hlt ⊢
            exact min_eq_right (le_of_not_ge fun hge => hlt.not_ge (min_eq_left hge).ge)
          obtain ⟨f₀, hf₀_cand, hf₀_eq⟩ := Finset.exists_mem_eq_inf'
            ⟨q.fare, mem_candFares_self q.fare fmax hist⟩
            (fun g => protectionControl fmin fmax n g - acceptedAtOrBelow g hist)
          have hf₀_Icc := candFares_subset_Icc q.fare fmax hq_fare.2 hist hf₀_cand
          have hf₀_full : f₀ ∈ Set.Icc fmin fmax := ⟨le_trans hq_fare.1 hf₀_Icc.1, hf₀_Icc.2⟩
          obtain ⟨h1, h2⟩ := ih_Q f₀ hf₀_full
          have htight_step : acceptedAtOrBelow f₀ (hist ++ [(q, y)]) = protectionControl fmin fmax n f₀ := by
            rw [acceptedAtOrBelow_append_singleton, if_pos hf₀_Icc.1, hy_eq_M]
            linarith [hf₀_eq]
          exact ⟨f₀, hf₀_Icc, by linarith⟩
      · exact Or.inr htight

-- Peeling from the maximum fare g_max in M
lemma filter_lt_max_props (g_max : ℝ) :
    ∀ (M : List (Request × ℝ)),
      (∀ e ∈ M, e.1.fare ≤ g_max ∧ 0 ≤ e.2) →
      0 ≤ acceptedTotal (M.filter (fun e => decide (e.1.fare < g_max))) ∧
      acceptedTotal (M.filter (fun e => decide (e.1.fare < g_max))) ≤ acceptedTotal M ∧
      acceptedAtOrBelow g_max M = acceptedTotal M ∧
      (M.map fun e => e.1.fare * e.2).sum =
        ((M.filter (fun e => decide (e.1.fare < g_max))).map fun e => e.1.fare * e.2).sum +
          g_max * (acceptedTotal M - acceptedTotal (M.filter (fun e => decide (e.1.fare < g_max)))) ∧
      (∀ f < g_max, acceptedAtOrBelow f (M.filter (fun e => decide (e.1.fare < g_max))) = acceptedAtOrBelow f M)
  | [], _ => by simp [acceptedTotal, acceptedAtOrBelow]
  | e :: es, hM => by
    have he := hM e List.mem_cons_self
    have hes : ∀ x ∈ es, x.1.fare ≤ g_max ∧ 0 ≤ x.2 := fun x hx => hM x (List.mem_cons_of_mem _ hx)
    obtain ⟨ih1, ih2, ih3, ih4, ih5⟩ := filter_lt_max_props g_max es hes
    unfold acceptedTotal at ih1 ih2 ih3 ih4 ⊢
    by_cases hlt : e.1.fare < g_max
    · simp only [List.filter_cons, decide_eq_true_eq, if_pos hlt, List.map_cons, List.sum_cons]
      refine ⟨add_nonneg he.2 ih1, by linarith, ?_, by linarith, fun f hf_lt => ?_⟩
      · unfold acceptedAtOrBelow at ih3 ⊢
        simp only [List.filter_cons, decide_eq_true_eq, if_pos he.1, List.map_cons, List.sum_cons, ih3]
      · have h1 := ih5 f hf_lt
        unfold acceptedAtOrBelow at h1 ⊢
        by_cases hfe : e.1.fare ≤ f
        · simp only [List.filter_cons, decide_eq_true_eq, if_pos hfe, List.map_cons, List.sum_cons, h1]
        · simp only [List.filter_cons, decide_eq_true_eq, if_neg hfe, h1]
    · have heq : e.1.fare = g_max := le_antisymm he.1 (not_lt.mp hlt)
      simp only [List.filter_cons, decide_eq_true_eq, if_neg hlt, List.map_cons, List.sum_cons]
      refine ⟨ih1, by linarith [he.2], ?_, ?_, fun f hf_lt => ?_⟩
      · unfold acceptedAtOrBelow at ih3 ⊢
        simp only [List.filter_cons, decide_eq_true_eq, if_pos he.1, List.map_cons, List.sum_cons, ih3]
      · rw [heq]; linarith
      · have hnot_le : ¬ (e.1.fare ≤ f) := by linarith
        have h1 := ih5 f hf_lt
        unfold acceptedAtOrBelow at h1 ⊢
        simp only [List.filter_cons, decide_eq_true_eq, if_neg hnot_le, h1]

lemma filter_lt_length_lt {g_max : ℝ} :
    ∀ {M : List (Request × ℝ)},
      (∃ e₀ ∈ M, e₀.1.fare = g_max) →
      (M.filter (fun e => decide (e.1.fare < g_max))).length < M.length
  | [], ⟨_, h, _⟩ => by simp at h
  | e :: es, ⟨e₀, he₀_mem, he₀_eq⟩ => by
    simp only [List.mem_cons] at he₀_mem
    rcases he₀_mem with rfl | he₀_es
    · have hnot : ¬ (e₀.1.fare < g_max) := by linarith
      simp only [List.filter_cons, decide_eq_true_eq, if_neg hnot, List.length_cons]
      exact Nat.lt_succ_of_le (List.length_filter_le _ _)
    · have ih := filter_lt_length_lt ⟨e₀, he₀_es, he₀_eq⟩
      by_cases hlt : e.1.fare < g_max
      · simp only [List.filter_cons, decide_eq_true_eq, if_pos hlt, List.length_cons]
        omega
      · simp only [List.filter_cons, decide_eq_true_eq, if_neg hlt, List.length_cons]
        omega

lemma V_le_rev_of_dominated (fmin fmax n : ℝ) (hfmin : 0 < fmin) (hf : fmin < fmax) (hn : 0 < n) :
    ∀ (k : ℕ) (M : List (Request × ℝ)),
      M.length ≤ k →
      (∀ e ∈ M, e.1.fare ∈ Set.Icc fmin fmax ∧ 0 ≤ e.2) →
      (∀ e ∈ M, acceptedAtOrBelow e.1.fare M ≤ protectionControl fmin fmax n e.1.fare) →
      valueAccumulation fmin fmax n (acceptedTotal M) ≤ (M.map fun e => e.1.fare * e.2).sum
  | 0, M, hlen, _, _ => by
    have hnil : M = [] := List.eq_nil_of_length_eq_zero (by omega)
    subst hnil
    simp [acceptedTotal, V_zero]
  | k + 1, M, hlen, hM_bds, hM_Q => by
    classical
    by_cases hM_nil : M = []
    · subst hM_nil
      simp [acceptedTotal, V_zero]
    · set F_M := (M.map fun e => e.1.fare).toFinset
      have hF_ne : F_M.Nonempty := by
        rcases List.exists_mem_of_ne_nil M hM_nil with ⟨e, he⟩
        exact ⟨e.1.fare, List.mem_toFinset.mpr (List.mem_map_of_mem he)⟩
      let g_max := F_M.max' hF_ne
      have hg_in : g_max ∈ F_M := Finset.max'_mem F_M hF_ne
      simp only [F_M, List.mem_toFinset, List.mem_map] at hg_in
      rcases hg_in with ⟨e₀, he₀_mem, he₀_eq⟩
      have hg_Icc : g_max ∈ Set.Icc fmin fmax := he₀_eq ▸ (hM_bds e₀ he₀_mem).1
      have hM_le_g : ∀ e ∈ M, e.1.fare ≤ g_max ∧ 0 ≤ e.2 := by
        intro e he
        refine ⟨Finset.le_max' F_M e.1.fare (List.mem_toFinset.mpr (List.mem_map_of_mem he)),
          (hM_bds e he).2⟩
      obtain ⟨hMlt_0, hMlt_le, hacc_g, hrev_split, hacc_lt⟩ := filter_lt_max_props g_max M hM_le_g
      set M_lt := M.filter (fun e => decide (e.1.fare < g_max))
      have hlen_lt : M_lt.length < M.length := filter_lt_length_lt ⟨e₀, he₀_mem, he₀_eq⟩
      have hMlt_bds : ∀ e ∈ M_lt, e.1.fare ∈ Set.Icc fmin fmax ∧ 0 ≤ e.2 := by
        intro e he
        rw [List.mem_filter] at he
        exact hM_bds e he.1
      have hMlt_Q : ∀ e ∈ M_lt, acceptedAtOrBelow e.1.fare M_lt ≤ protectionControl fmin fmax n e.1.fare := by
        intro e he
        rw [List.mem_filter, decide_eq_true_eq] at he
        rw [hacc_lt e.1.fare he.2]
        exact hM_Q e he.1
      have ih := V_le_rev_of_dominated fmin fmax n hfmin hf hn k M_lt (by omega) hMlt_bds hMlt_Q
      have htot_le_Q : acceptedTotal M ≤ protectionControl fmin fmax n g_max := by
        rw [← hacc_g, ← he₀_eq]
        exact hM_Q e₀ he₀_mem
      have hV_step := V_diff_le_fare_mul fmin fmax n hfmin hf hn hg_Icc hMlt_0 hMlt_le htot_le_Q
      linarith

lemma filter_le_props (f₀ : ℝ) :
    ∀ (L : List (Request × ℝ)),
      acceptedTotal (L.filter (fun e => decide (e.1.fare ≤ f₀))) = acceptedAtOrBelow f₀ L ∧
      (∀ f ≤ f₀, acceptedAtOrBelow f (L.filter (fun e => decide (e.1.fare ≤ f₀))) = acceptedAtOrBelow f L) ∧
      (L.map fun e => e.1.fare * e.2).sum =
        ((L.filter (fun e => decide (e.1.fare ≤ f₀))).map fun e => e.1.fare * e.2).sum +
          (L.map fun e => if f₀ < e.1.fare then e.1.fare * e.2 else 0).sum
  | [] => by simp [acceptedTotal, acceptedAtOrBelow]
  | e :: es => by
    obtain ⟨ih1, ih2, ih3⟩ := filter_le_props f₀ es
    unfold acceptedTotal at ih1 ⊢
    by_cases hle : e.1.fare ≤ f₀
    · have hnot_gt : ¬ (f₀ < e.1.fare) := not_lt.mpr hle
      simp only [List.filter_cons, decide_eq_true_eq, if_pos hle, List.map_cons, List.sum_cons, if_neg hnot_gt]
      refine ⟨?_, fun f hf_le => ?_, by linarith⟩
      · unfold acceptedAtOrBelow at ih1 ⊢
        simp only [List.filter_cons, decide_eq_true_eq, if_pos hle, List.map_cons, List.sum_cons, ih1]
      · have h1 := ih2 f hf_le
        unfold acceptedAtOrBelow at h1 ⊢
        by_cases hfe : e.1.fare ≤ f
        · simp only [List.filter_cons, decide_eq_true_eq, if_pos hfe, List.map_cons, List.sum_cons, h1]
        · simp only [List.filter_cons, decide_eq_true_eq, if_neg hfe, h1]
    · have hgt : f₀ < e.1.fare := not_le.mp hle
      simp only [List.filter_cons, decide_eq_true_eq, if_neg hle, List.map_cons, List.sum_cons, if_pos hgt]
      refine ⟨?_, fun f hf_le => ?_, by linarith⟩
      · unfold acceptedAtOrBelow at ih1 ⊢
        simp only [List.filter_cons, decide_eq_true_eq, if_neg hle, ih1]
      · have hnot_fe : ¬ (e.1.fare ≤ f) := by linarith
        have h1 := ih2 f hf_le
        unfold acceptedAtOrBelow at h1 ⊢
        simp only [List.filter_cons, decide_eq_true_eq, if_neg hnot_fe, h1]

lemma protection_instance_bound (fmin fmax n : ℝ) (hfmin : 0 < fmin) (hf : fmin < fmax)
    (hn : 0 < n) (I : List Request) (hI : FaresIn (Set.Icc fmin fmax) I) :
    1 / (1 - Real.log (discountRatio fmin fmax)) * offlineOpt n I ≤
      revenue n (protectionLevelPolicy fmax (protectionControl fmin fmax n)) I := by
  obtain ⟨hρ_pos, hρ_lt1⟩ := rho_bounds fmin fmax hfmin hf
  change rho (discountRatio fmin fmax) * offlineOpt n I ≤ _
  set P_pol := protectionLevelPolicy fmax (protectionControl fmin fmax n)
  set L := run P_pol n I
  have hL_inv : (∀ e ∈ L, e.1.fare ∈ Set.Icc fmin fmax ∧ 0 ≤ e.2 ∧ e.2 ≤ e.1.qty) ∧
      acceptedTotal L ≤ n :=
    runFrom_inv fmin fmax n P_pol I [] hI (by simp) (by simp [acceptedTotal, hn.le])
  have hQ_init : ∀ f ∈ Set.Icc fmin fmax, acceptedAtOrBelow f [] ≤ protectionControl fmin fmax n f := by
    intro f hf_mem
    simpa [acceptedAtOrBelow] using Q_nonneg fmin fmax n hfmin hf hn hf_mem
  obtain ⟨hL_Q, hL_tight⟩ := runFrom_protection_props fmin fmax n hfmin hf hn I [] hI (by simp) hQ_init
  rcases all_full_or_max_rejected fmin fmax L hL_inv.1 with hfull | ⟨f', hf'_mem, ⟨e₀, he₀_mem, he₀_fare, he₀_lt⟩, hfull_gt⟩
  · -- Case 1: all requests accepted in full
    have hrev_eq : revenue n P_pol I = (I.map fun q => q.fare * q.qty).sum := by
      unfold revenue
      have hcongr : L.map (fun e => e.1.fare * e.2) = L.map (fun e => e.1.fare * e.1.qty) := by
        apply List.map_congr_left
        intro e he
        rw [hfull e he]
      rw [hcongr, map_fst_comp L (fun q => q.fare * q.qty), run_map_fst]
    have hopt_le := offlineOpt_le_full fmin fmax n hfmin hn hI
    have hopt_nonneg := offlineOpt_nonneg n hn I
    calc rho (discountRatio fmin fmax) * offlineOpt n I
        ≤ 1 * offlineOpt n I := mul_le_mul_of_nonneg_right hρ_lt1.le hopt_nonneg
      _ = offlineOpt n I := one_mul _
      _ ≤ (I.map fun q => q.fare * q.qty).sum := hopt_le
      _ = revenue n P_pol I := hrev_eq.symm
  · -- Case 2: some request of fare f' not accepted in full
    rcases hL_tight e₀ he₀_mem he₀_lt with he₀_nil | ⟨f₀, hf₀_Icc, hf₀_tight⟩
    · simp at he₀_nil
    · rw [he₀_fare] at hf₀_Icc
      have hf₀_mem : f₀ ∈ Set.Icc fmin fmax := ⟨le_trans hf'_mem.1 hf₀_Icc.1, hf₀_Icc.2⟩
      obtain ⟨hM_tot, hM_acc, hrev_split⟩ := filter_le_props f₀ L
      set M := L.filter (fun e => decide (e.1.fare ≤ f₀))
      have hM_bds : ∀ e ∈ M, e.1.fare ∈ Set.Icc fmin fmax ∧ 0 ≤ e.2 := by
        intro e he
        rw [List.mem_filter] at he
        exact ⟨(hL_inv.1 e he.1).1, (hL_inv.1 e he.1).2.1⟩
      have hM_Q : ∀ e ∈ M, acceptedAtOrBelow e.1.fare M ≤ protectionControl fmin fmax n e.1.fare := by
        intro e he
        rw [List.mem_filter, decide_eq_true_eq] at he
        rw [hM_acc e.1.fare he.2]
        exact (hL_Q e.1.fare (hL_inv.1 e he.1).1).2
      have htail_ge : rho (discountRatio fmin fmax) * (f₀ * n) ≤ (M.map fun e => e.1.fare * e.2).sum := by
        have hV := V_le_rev_of_dominated fmin fmax n hfmin hf hn M.length M le_rfl hM_bds hM_Q
        change acceptedAtOrBelow f₀ L = protectionControl fmin fmax n f₀ at hf₀_tight
        rw [hM_tot, hf₀_tight, V_Q_eq fmin fmax n hfmin hf hn hf₀_mem] at hV
        exact hV
      have hhead_eq :
          (L.map fun e => if f₀ < e.1.fare then e.1.fare * e.2 else 0).sum =
            (I.map fun q => if f₀ < q.fare then q.fare * q.qty else 0).sum := by
        have hcongr :
            L.map (fun e => if f₀ < e.1.fare then e.1.fare * e.2 else 0) =
              L.map (fun e => if f₀ < e.1.fare then e.1.fare * e.1.qty else 0) := by
          apply List.map_congr_left
          intro e he
          split_ifs with hgt
          · rw [hfull_gt e he (lt_of_le_of_lt hf₀_Icc.1 hgt)]
          · rfl
        rw [hcongr, map_fst_comp L (fun q => if f₀ < q.fare then q.fare * q.qty else 0),
          run_map_fst]
      have hhead_ge_diff := sum_diff_le_sum_full fmin fmax hfmin hf₀_mem I
      have hdiff_nonneg :
          0 ≤ (I.map fun q => if f₀ < q.fare then (q.fare - f₀) * q.qty else 0).sum := by
        apply List.sum_nonneg
        intro x hx
        rw [List.mem_map] at hx
        rcases hx with ⟨q, _, rfl⟩
        split_ifs with hgt
        · exact mul_nonneg (by linarith) q.qty_pos.le
        · exact le_rfl
      have hopt_le := offlineOpt_le_split fmin fmax n hfmin hn hf₀_mem (I := I)
      unfold revenue
      set S_diff := (I.map fun q => if f₀ < q.fare then (q.fare - f₀) * q.qty else 0).sum
      calc rho (discountRatio fmin fmax) * offlineOpt n I
          ≤ rho (discountRatio fmin fmax) * (f₀ * n + S_diff) :=
            mul_le_mul_of_nonneg_left hopt_le hρ_pos.le
        _ = rho (discountRatio fmin fmax) * (f₀ * n) + rho (discountRatio fmin fmax) * S_diff := by ring
        _ ≤ rho (discountRatio fmin fmax) * (f₀ * n) + 1 * S_diff := by
            linarith [mul_le_mul_of_nonneg_right hρ_lt1.le hdiff_nonneg]
        _ ≤ (M.map fun e => e.1.fare * e.2).sum +
              (L.map fun e => if f₀ < e.1.fare then e.1.fare * e.2 else 0).sum := by
            rw [one_mul, hhead_eq]
            linarith [htail_ge, hhead_ge_diff]
        _ = (L.map fun e => e.1.fare * e.2).sum := hrev_split.symm

end Aux_RB_thm7

namespace RobustBooking.BidPrice

open Aux_RB_thm7

theorem theorem7_bid_price_competitive (fmin fmax n : ℝ) (hfmin : 0 < fmin) (hf : fmin < fmax)
    (hn : 0 < n) (I : List Request) (hI : FaresIn (Set.Icc fmin fmax) I) :
    1 / (1 - Real.log (discountRatio fmin fmax)) * offlineOpt n I ≤
        revenue n (protectionLevelPolicy fmax (protectionControl fmin fmax n)) I ∧
      1 / (1 - Real.log (discountRatio fmin fmax)) * offlineOpt n I ≤
        revenue n (orderQuantityPolicy fmin fmax n (protectionControl fmin fmax n)) I :=
  ⟨protection_instance_bound fmin fmax n hfmin hf hn I hI,
   orderQuantity_instance_bound fmin fmax n hfmin hf hn I hI⟩

end RobustBooking.BidPrice

open RobustBooking.BidPrice in
theorem solution (fmin fmax n : ℝ) (hfmin : 0 < fmin) (hf : fmin < fmax)
    (hn : 0 < n) (I : List Request) (hI : FaresIn (Set.Icc fmin fmax) I) :
    1 / (1 - Real.log (discountRatio fmin fmax)) * offlineOpt n I ≤
        revenue n (protectionLevelPolicy fmax (protectionControl fmin fmax n)) I ∧
      1 / (1 - Real.log (discountRatio fmin fmax)) * offlineOpt n I ≤
        revenue n (orderQuantityPolicy fmin fmax n (protectionControl fmin fmax n)) I :=
  theorem7_bid_price_competitive fmin fmax n hfmin hf hn I hI
