-- Prove2me | solution 1 for PlatformFinance.WinWin.proposition_4
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-24T00:12:50.052361+00:00
-- url     : https://prove2.me/submissions/21242abb-7b5b-44f5-a20a-34c84676af7d

import Mathlib
import Definitions.Def_PlatformFinance_WinWin_Model
import Theorems.Thm_PlatformFinance_WinWin_proposition_3

/-!
Proposition 4 of Huang, Lai, Wang & Xiao (SSRN 4014045, p. 18): reduction to Proposition 3
(`PlatformFinance.WinWin.proposition_3`, parts 1 and 2: the comparison of the seller's unit
debt and order quantity in the two games). The step from those comparisons to the seller's
profits (monotonicity of the seller payoff in the per-unit debt) is proved here in full.
-/

set_option autoImplicit false

namespace PFW4
open PlatformFinance.WinWin

lemma integrand_cont (φ W q : ℝ) :
    Continuous (fun x : ℝ => max ((1 - φ) * (x - q) * q - W * q) 0) := by
  fun_prop

lemma payoff_zero (a δ φ W : ℝ) : sellerPayoff a δ φ W 0 = 0 := by
  simp [sellerPayoff, uniformMean]

/-- Weak monotonicity: owing more per unit never helps the seller. -/
lemma payoff_anti (a δ φ W W' q : ℝ) (hδ : 0 < δ) (hq : 0 ≤ q) (hW : W ≤ W') :
    sellerPayoff a δ φ W' q ≤ sellerPayoff a δ φ W q := by
  unfold sellerPayoff uniformMean
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply intervalIntegral.integral_mono_on (by linarith)
    ((integrand_cont φ W' q).intervalIntegrable _ _)
    ((integrand_cont φ W q).intervalIntegrable _ _)
  intro x _
  apply max_le_max _ le_rfl
  nlinarith

lemma pointwise_gain (φ W W' q x xmax M : ℝ) (hφ1 : φ < 1) (hq : 0 ≤ q) (hW : W < W')
    (hx : x ≤ xmax) (hM : max ((1 - φ) * (xmax - q) * q - W' * q) 0 < M) :
    (1 + (W' - W) * q / M) * max ((1 - φ) * (x - q) * q - W' * q) 0 ≤
      max ((1 - φ) * (x - q) * q - W * q) 0 := by
  have hM0 : 0 < M := lt_of_le_of_lt (le_max_right _ _) hM
  have hk : 0 ≤ (W' - W) * q := mul_nonneg (by linarith) hq
  have hmono : (1 - φ) * (x - q) * q - W' * q ≤ (1 - φ) * (xmax - q) * q - W' * q := by
    have : 0 ≤ (1 - φ) * q := mul_nonneg (by linarith) hq
    nlinarith
  rcases le_or_gt ((1 - φ) * (x - q) * q - W' * q) 0 with h | h
  · rw [max_eq_right h]; simp
  · rw [max_eq_left h.le]
    have hfM : (1 - φ) * (x - q) * q - W' * q ≤ M :=
      le_trans hmono (le_trans (le_max_left _ _) hM.le)
    have hc : (W' - W) * q / M * ((1 - φ) * (x - q) * q - W' * q) ≤ (W' - W) * q := by
      rw [div_mul_eq_mul_div, div_le_iff₀ hM0]
      exact mul_le_mul_of_nonneg_left hfM hk
    have : (1 - φ) * (x - q) * q - W' * q + (W' - W) * q ≤
        max ((1 - φ) * (x - q) * q - W * q) 0 := by
      apply le_trans _ (le_max_left _ _); linarith
    nlinarith

/-- Strict monotonicity where the payoff is positive. -/
lemma payoff_strict (a δ φ W W' q : ℝ) (hδ : 0 < δ) (hφ1 : φ < 1) (hq : 0 ≤ q) (hW : W < W')
    (hpos : 0 < sellerPayoff a δ φ W' q) :
    sellerPayoff a δ φ W' q < sellerPayoff a δ φ W q := by
  have hq0 : q ≠ 0 := by
    rintro rfl; rw [payoff_zero] at hpos; exact lt_irrefl _ hpos
  have hqp : 0 < q := lt_of_le_of_ne hq (Ne.symm hq0)
  set M := max ((1 - φ) * (a + δ - q) * q - W' * q) 0 + 1 with hMdef
  have hM : max ((1 - φ) * (a + δ - q) * q - W' * q) 0 < M := by rw [hMdef]; linarith
  have hM0 : 0 < M := lt_of_le_of_lt (le_max_right _ _) hM
  set c := (W' - W) * q / M with hcdef
  have hc : 0 < c := div_pos (mul_pos (by linarith) hqp) hM0
  have key : (1 + c) * sellerPayoff a δ φ W' q ≤ sellerPayoff a δ φ W q := by
    unfold sellerPayoff uniformMean
    rw [show (1 + c) * ((2 * δ)⁻¹ * ∫ x in (a - δ)..(a + δ),
        max ((1 - φ) * (x - q) * q - W' * q) 0) =
        (2 * δ)⁻¹ * ∫ x in (a - δ)..(a + δ),
          (1 + c) * max ((1 - φ) * (x - q) * q - W' * q) 0 by
      rw [intervalIntegral.integral_const_mul]; ring]
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    apply intervalIntegral.integral_mono_on (by linarith)
      (((integrand_cont φ W' q).const_smul (1 + c)).intervalIntegrable _ _)
      ((integrand_cont φ W q).intervalIntegrable _ _)
    intro x hx
    exact pointwise_gain φ W W' q x (a + δ) M hφ1 hq hW hx.2 hM
  nlinarith

/-- Proposition 4 from the order/price comparison of Proposition 3 (parts 1 and 2). -/
theorem prop4_of_prop3 (a δ φ c rf : ℝ) (hδ : 0 < δ) (hφ1 : φ < 1)
    (r : ℝ) (σT σP : Profile) (hT : IsSPET a δ φ c rf σT) (hP : IsSPEP a δ φ c rf r σP)
    (H1 : r < rhat1 a δ φ c rf →
        σP.w * (1 + r) < σT.w ∧ σT.order σT.w < σP.order σP.w)
    (H2 : rhat1 a δ φ c rf < r ∨
          (r = rhat1 a δ φ c rf ∧ (δ ≤ delta2 a φ c rf ∨ delta3 a φ c rf < δ)) →
        σT.w ≤ σP.w * (1 + r) ∧ σP.order σP.w ≤ σT.order σT.w) :
    (r < rhat1 a δ φ c rf → sellerProfitT a δ φ σT < sellerProfitP a δ φ r σP) ∧
      (rhat1 a δ φ c rf < r ∨
          (r = rhat1 a δ φ c rf ∧ (δ ≤ delta2 a φ c rf ∨ delta3 a φ c rf < δ)) →
        sellerProfitP a δ φ r σP ≤ sellerProfitT a δ φ σT) := by
  obtain ⟨hTs, -, -⟩ := hT
  obtain ⟨hPs, -, -⟩ := hP
  obtain ⟨hTq0, hTopt, -⟩ := hTs σT.w
  obtain ⟨hPq0, hPopt, hPtie⟩ := hPs σP.w
  simp only at hTopt hPopt hPtie
  unfold sellerProfitT sellerProfitP
  refine ⟨fun hr => ?_, fun hc => ?_⟩
  · obtain ⟨hw, hq⟩ := H1 hr
    rcases lt_or_ge 0 (sellerPayoff a δ φ σT.w (σT.order σT.w)) with hpos | hnp
    · calc sellerPayoff a δ φ σT.w (σT.order σT.w)
          < sellerPayoff a δ φ (σP.w * (1 + r)) (σT.order σT.w) :=
            payoff_strict a δ φ _ _ _ hδ hφ1 hTq0 hw hpos
        _ ≤ sellerPayoff a δ φ (σP.w * (1 + r)) (σP.order σP.w) := hPopt _ hTq0
    · have hne : σP.order σP.w ≠ 0 := by
        intro h; rw [h] at hq; linarith
      have : ¬ ∀ q : ℝ, 0 ≤ q → sellerPayoff a δ φ (σP.w * (1 + r)) q ≤ 0 :=
        fun hall => hne (hPtie hall)
      push_neg at this
      obtain ⟨q0, hq0, hq0p⟩ := this
      linarith [hPopt q0 hq0]
  · obtain ⟨hw, -⟩ := H2 hc
    calc sellerPayoff a δ φ (σP.w * (1 + r)) (σP.order σP.w)
        ≤ sellerPayoff a δ φ σT.w (σP.order σP.w) := payoff_anti a δ φ _ _ _ hδ hPq0 hw
      _ ≤ sellerPayoff a δ φ σT.w (σT.order σT.w) := hTopt _ hPq0

end PFW4

open PlatformFinance.WinWin in
theorem solution (a δ φ c rf : ℝ) (hδ : 0 < δ) (hδa : δ < a) (hφ0 : 0 ≤ φ) (hφ1 : φ < 1) (hc : 0 < c)
    (hrf : 0 ≤ rf) (hprof : c * (1 + rf) < (1 - φ) * a)
    (r : ℝ) (hr : -1 < r) (hrq : c * (1 + r) < (a + δ) * (1 - φ))
    (σT σP : Profile) (hT : IsSPET a δ φ c rf σT) (hP : IsSPEP a δ φ c rf r σP) :
    (r < rhat1 a δ φ c rf → sellerProfitT a δ φ σT < sellerProfitP a δ φ r σP) ∧
      (rhat1 a δ φ c rf < r ∨
          (r = rhat1 a δ φ c rf ∧ (δ ≤ delta2 a φ c rf ∨ delta3 a φ c rf < δ)) →
        sellerProfitP a δ φ r σP ≤ sellerProfitT a δ φ σT) := by
  obtain ⟨H1, H2, -⟩ :=
    proposition_3 a δ φ c rf hδ hδa hφ0 hφ1 hc hrf hprof r hr hrq σT σP hT hP
  exact PFW4.prop4_of_prop3 a δ φ c rf hδ hφ1 r σT σP hT hP H1 H2
