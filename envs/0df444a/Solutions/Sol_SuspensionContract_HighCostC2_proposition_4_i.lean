-- Prove2me | solution 1 for SuspensionContract.HighCostC2.proposition_4_i
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-23T22:48:30.032512+00:00
-- url     : https://prove2.me/submissions/71c2c245-0ad6-4d85-9014-4f499585852e

import Mathlib
import Definitions.Def_SuspensionContract_HighCostC2_Setting
import Theorems.Thm_SuspensionContract_HighCostC2_lemma_EC_2_vi_equiv

open SuspensionContract.HighCostC2

namespace HC2Prop4Aux

lemma dW_lin (f : ℝ → ℝ) (a m w : ℝ) (h : ∀ x ≤ w, f x = a + m * x) :
    derivWithin f (Set.Iic w) w = m := by
  have hd : HasDerivWithinAt (fun x : ℝ => a + m * x) m (Set.Iic w) w := by
    have := ((hasDerivAt_id w).const_mul m).const_add a
    simpa using this.hasDerivWithinAt
  have hd2 : HasDerivWithinAt f m (Set.Iic w) w :=
    hd.congr_of_mem (fun x hx => h x hx) (Set.mem_Iic.mpr le_rfl)
  exact hd2.derivWithin (uniqueDiffWithinAt_Iic w)

lemma dW_const (f : ℝ → ℝ) (C t w : ℝ) (htw : t < w) (h : ∀ x, t < x → f x = C) :
    derivWithin f (Set.Iic w) w = 0 := by
  have hev : f =ᶠ[nhdsWithin w (Set.Iic w)] (fun _ => C) := by
    apply eventually_nhdsWithin_of_eventually_nhds
    filter_upwards [Ioi_mem_nhds htw] with x hx using h x hx
  rw [hev.derivWithin_eq (h w htw)]
  simp

/-- Basic facts under the standing assumptions and Condition 2. -/
lemma basics (P : Params) (hP : P.Standing) (h2 : P.Condition2) :
    0 < P.β ∧ 0 < P.wbar ∧ P.wbar < P.β ∧ 0 < P.r ∧ P.r < P.ρ ∧ P.μ < P.ρ - P.r ∧
      P.r * P.Vbar = P.R * P.μ - P.c - (P.ρ - P.r) * P.wbar ∧ P.r * P.vlow = P.μlow * P.R ∧
      (P.ρ - P.r) * P.wbar ≤ (P.ρ - P.r - P.μ) * (P.Vbar - P.vlow) := by
  obtain ⟨⟨hl0, hlμ⟩, ⟨hb, hbc⟩, hK, ⟨hr, hrρ⟩, hA⟩ := hP
  obtain ⟨hc2, hR⟩ := h2
  have hμ : 0 < P.μ := lt_of_le_of_lt hl0 hlμ
  have hρ : 0 < P.ρ := by linarith
  have hΔ : 0 < P.Δμ := by unfold Params.Δμ; linarith
  have hβ : 0 < P.β := by unfold Params.β; positivity
  have hw : 0 < P.wbar := by unfold Params.wbar; positivity
  have hwβ : P.wbar < P.β := by
    unfold Params.wbar; rw [div_lt_iff₀ hρ]; nlinarith
  have hV : P.r * P.Vbar = P.R * P.μ - P.c - (P.ρ - P.r) * P.wbar := by
    unfold Params.Vbar; field_simp
  have hv : P.r * P.vlow = P.μlow * P.R := by unfold Params.vlow; field_simp
  have hE := (lemma_EC_2_vi_equiv P ⟨⟨hl0, hlμ⟩, ⟨hb, hbc⟩, hK, ⟨hr, hrρ⟩, hA⟩ (by linarith)).mpr hR
  have hpos : 0 < P.ρ - P.r - P.μ := by linarith
  have key : (P.ρ - P.r) * P.wbar ≤ (P.ρ - P.r - P.μ) * (P.Vbar - P.vlow) := by
    have : (P.ρ - P.r) / (P.ρ - P.r - P.μ) * P.wbar ≤ P.Vbar - P.vlow := by linarith
    rw [div_mul_eq_mul_div, div_le_iff₀ hpos] at this
    linarith
  exact ⟨hβ, hw, hwβ, hr, by linarith, hc2, hV, hv, key⟩

/-- The working-state inequality `(𝒜_I V_I)(w) ≥ 0` for `w > 0`. -/
lemma AI_nonneg (P : Params) (hP : P.Standing) (h2 : P.Condition2) (w : ℝ) (hw0 : 0 < w) :
    0 ≤ P.AI P.VI31 w := by
  obtain ⟨hβ, hw, hwβ, hr, hrρ, hc2, hV, hv, key⟩ := basics P hP h2
  set s := (P.Vbar - P.vlow) / P.wbar with hs
  have hsw : s * P.wbar = P.Vbar - P.vlow := by rw [hs]; field_simp
  have hplus : P.VI31 (w + P.β) = P.Vbar := by
    unfold Params.VI31; rw [if_neg (by linarith)]
  unfold Params.AI
  rw [hplus]
  rcases le_or_gt w P.wbar with hle | hlt
  · have hd : derivWithin P.VI31 (Set.Iic w) w = s := by
      apply dW_lin _ P.vlow s w
      intro x hx; unfold Params.VI31; rw [if_pos (le_trans hx hle)]
    rw [hd]
    have hf : P.VI31 w = P.vlow + s * w := by unfold Params.VI31; rw [if_pos hle]
    rw [hf]
    -- AI = (w̄ - w) (s(ρ-r-μ) - (ρ-r))
    have hkey : (P.ρ - P.r) * P.wbar ≤ (P.ρ - P.r - P.μ) * (s * P.wbar) := by rw [hsw]; exact key
    have hk2 : (P.ρ - P.r) ≤ (P.ρ - P.r - P.μ) * s := by
      have : (P.ρ - P.r) * P.wbar ≤ ((P.ρ - P.r - P.μ) * s) * P.wbar := by linarith
      exact le_of_mul_le_mul_right this hw
    have hexp : (P.μ + P.r) * (P.vlow + s * w) - P.μ * P.Vbar + P.ρ * (P.wbar - w) * s
        - (P.μ * P.R - P.c) + (P.ρ - P.r) * w
        = (P.wbar - w) * ((P.ρ - P.r - P.μ) * s - (P.ρ - P.r)) := by
      have hVb : P.Vbar = P.vlow + s * P.wbar := by linarith
      rw [hVb]; rw [hVb] at hV; nlinarith [hV, hv]
    rw [hexp]
    exact mul_nonneg (by linarith) (by linarith)
  · have hd : derivWithin P.VI31 (Set.Iic w) w = 0 := by
      apply dW_const _ P.Vbar P.wbar w hlt
      intro x hx; unfold Params.VI31; rw [if_neg (by linarith)]
    rw [hd]
    have hf : P.VI31 w = P.Vbar := by unfold Params.VI31; rw [if_neg (by linarith)]
    rw [hf]
    nlinarith

lemma VI_diff_bounds (P : Params) (hP : P.Standing) (h2 : P.Condition2) (w : ℝ) (hw0 : 0 ≤ w) :
    P.vlow ≤ P.VI31 w ∧ P.VI31 w ≤ P.Vbar := by
  obtain ⟨hβ, hw, hwβ, hr, hrρ, hc2, hV, hv, key⟩ := basics P hP h2
  have hVv : 0 ≤ P.Vbar - P.vlow := by
    by_contra hc
    have hneg : (P.ρ - P.r - P.μ) * (P.Vbar - P.vlow) < 0 :=
      mul_neg_of_pos_of_neg (by linarith) (by linarith)
    nlinarith [mul_pos (sub_pos.2 hrρ) hw]
  unfold Params.VI31
  split_ifs with h
  · have h1 : 0 ≤ (P.Vbar - P.vlow) / P.wbar * w := by positivity
    have h2' : (P.Vbar - P.vlow) / P.wbar * w ≤ P.Vbar - P.vlow := by
      rw [div_mul_eq_mul_div, div_le_iff₀ hw]; nlinarith
    constructor <;> linarith
  · constructor <;> linarith

end HC2Prop4Aux

open HC2Prop4Aux in
theorem solution (P : Params) (hP : P.Standing) (h2 : P.Condition2)
    (hK : P.Vbar - P.vlow < P.K) : P.OptCond P.VI31 (fun _ => P.vlow) := by
  obtain ⟨hβ, hw, hwβ, hr, hrρ, hc2, hV, hv, key⟩ := basics P hP h2
  refine ⟨fun w hw0 => ⟨AI_nonneg P hP h2 w hw0, ?_⟩, fun w hw0 => ?_, ?_, le_rfl⟩
  · unfold Params.A0
    have h0 : derivWithin (fun _ : ℝ => P.vlow) (Set.Iic w) w = 0 := by simp
    rw [h0]
    nlinarith
  · obtain ⟨a, b⟩ := VI_diff_bounds P hP h2 w hw0
    constructor <;> linarith
  · unfold Params.VI31; rw [if_pos hw.le]; simp
