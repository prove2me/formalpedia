-- Prove2me | solution 1 for TokenFinance.MoralHazard.proposition_7
-- status  : ACCEPTED   (prove)
-- author  : @mihalyimark
-- created : 2026-10-19T12:35:17.455994+00:00
-- url     : https://prove2.me/submissions/e8be9574-e9e5-4cb6-b7e8-6ca7cefb09ff

/-
DS19H proof of the MoralHazard milestone TokenFinance.MoralHazard.proposition_7
(theorem_id d58cb45a-b9c2-4574-90f6-17bdf2d48050), Proposition 7 / equation (29).

Mathematics.  Put L = θh − c > 0, τ = 2t/L and λ = (θl − c)/L.  The accepted
platform milestone `token_expected_profit` gives the entrepreneur's expected
profit under the token contract at `θ`:
  c/(c+t) · 2/(3θ) · ((θ−c)/2 − t)³   if c + 2t ≤ θ,   and 0 if θ ≤ c + 2t.
At θh the break-even condition (16) plus the accepted `Debt.eq_3` identify this
expectation with NPV_h.  At θl ≤ c+2t (i.e. λ ≤ τ) it is zero, so the effort
condition reduces to NPV_h − Ce ≥ 0.  When τ < λ, the low-demand expectation is
  c/(c+t) · L³/(12θl) · (λ−τ)³,
and the θh break-even relation c/(c+t) · L³/(12θh) · (1−τ)³ = NPV_h turns it
into (λ−τ)³/(1−τ)³ · (θh/θl) · NPV_h.  This yields (29) and both cases.
-/
import Mathlib
import Definitions.Def_TokenFinance_Debt_Setting
import Definitions.Def_TokenFinance_MoralHazard_Financeable
import Theorems.Thm_TokenFinance_Debt_eq_3
import Theorems.Thm_TokenFinance_MoralHazard_token_expected_profit

open TokenFinance.MoralHazard

theorem solution (c C0 Ce θl θh t τ lam : ℝ) (hA : MHAssumptions c C0 Ce θl θh)
    (ht0 : 0 < t) (ht1 : t < (θh - c) / 2) (hBE : TokenFinance.Debt.tokenBreakEven c C0 θh t)
    (hτ : τ = 2 * t / (θh - c)) (hlam : lam = (θl - c) / (θh - c)) :
    (lam ≤ τ →
      TokenFinance.Debt.expect θh (fun x => TokenFinance.Debt.tokEnt c t x (TokenFinance.Debt.qm c x)) - Ce ≥
          TokenFinance.Debt.expect θl (fun x => TokenFinance.Debt.tokEnt c t x (TokenFinance.Debt.qm c x)) ∧
        TokenFinanceable c C0 Ce θl θh) ∧
    (τ < lam →
      (TokenFinance.Debt.expect θh (fun x => TokenFinance.Debt.tokEnt c t x (TokenFinance.Debt.qm c x)) - Ce ≥
          TokenFinance.Debt.expect θl (fun x => TokenFinance.Debt.tokEnt c t x (TokenFinance.Debt.qm c x)) ↔
        TokenFinance.Debt.npv c C0 θh - Ce ≥ (lam - τ) ^ 3 / (1 - τ) ^ 3 * (θh / θl) * TokenFinance.Debt.npv c C0 θh)) := by
  obtain ⟨hc, hcθl, hθlθh, hC0, hnpvl, hnpvh, hCe⟩ := hA
  have hcθh : c < θh := lt_trans hcθl hθlθh
  have hθh : 0 < θh := lt_trans hc hcθh
  have hθl : 0 < θl := lt_trans hc hcθl
  have hL : 0 < θh - c := by linarith
  have hLne : θh - c ≠ 0 := ne_of_gt hL
  have hθhne : θh ≠ 0 := ne_of_gt hθh
  have hθlne : θl ≠ 0 := ne_of_gt hθl
  have hct : c + t ≠ 0 := by positivity
  -- theta_h > c + 2t
  have hc2t : c + 2 * t < θh := by linarith
  have hτ0 : 0 < τ := by
    rw [hτ]
    exact div_pos (by positivity) hL
  have hτ1 : τ < 1 := by
    rw [hτ, div_lt_one hL]
    linarith
  have hθl_eq : θl - c = lam * (θh - c) := by
    rw [hlam]
    field_simp [hLne]
  have ht_eq : 2 * t = τ * (θh - c) := by
    rw [hτ]
    field_simp [hLne]
  -- expectations at theta_h
  have hTEh := (token_expected_profit c t θh hc ht0 hθh).1 hc2t.le
  have hE3 := TokenFinance.Debt.eq_3 c C0 θh hc hcθh
  have hEθh : TokenFinance.Debt.expect θh (fun x => TokenFinance.Debt.tokEnt c t x (TokenFinance.Debt.qm c x))
      = TokenFinance.Debt.npv c C0 θh := by
    rw [hTEh, hE3]
    exact hBE
  -- normalized break-even coefficient
  have hargh : (θh - c) / 2 - t = (θh - c) * (1 - τ) / 2 := by linarith
  have hnpv_norm : TokenFinance.Debt.npv c C0 θh
      = c / (c + t) * ((θh - c) ^ 3 * (1 - τ) ^ 3 / (12 * θh)) := by
    rw [← hEθh, hTEh, hargh]
    field_simp [hθhne]
    ring
  have hcct : c / (c + t)
      = TokenFinance.Debt.npv c C0 θh * (12 * θh) / ((θh - c) ^ 3 * (1 - τ) ^ 3) := by
    rw [hnpv_norm]
    have hL3 : (θh - c) ^ 3 ≠ 0 := pow_ne_zero 3 hLne
    have h1t : (1 - τ) ^ 3 ≠ 0 := pow_ne_zero 3 (by linarith : (1 : ℝ) - τ ≠ 0)
    field_simp [hθhne, hL3, h1t, (by linarith : (1 : ℝ) - τ ≠ 0)]
  constructor
  · -- case lambda <= tau
    intro hlamτ
    have hle : θl ≤ c + 2 * t := by
      have h1 : lam * (θh - c) ≤ τ * (θh - c) :=
        mul_le_mul_of_nonneg_right hlamτ hL.le
      have : θl - c ≤ 2 * t := by rw [hθl_eq]; linarith
      linarith
    have hEθl0 := (token_expected_profit c t θl hc ht0 hθl).2 hle
    have hinc : TokenFinance.Debt.expect θh (fun x => TokenFinance.Debt.tokEnt c t x (TokenFinance.Debt.qm c x)) - Ce ≥
        TokenFinance.Debt.expect θl (fun x => TokenFinance.Debt.tokEnt c t x (TokenFinance.Debt.qm c x)) := by
      rw [hEθl0, hEθh]
      linarith
    exact ⟨hinc, ⟨t, ht0, ht1, hBE, hinc⟩⟩
  · -- case tau < lambda
    intro hτlam
    have hgt : c + 2 * t < θl := by
      have h1 : τ * (θh - c) < lam * (θh - c) :=
        mul_lt_mul_of_pos_right hτlam hL
      have : 2 * t < θl - c := by rw [hθl_eq]; linarith
      linarith
    have hTE := (token_expected_profit c t θl hc ht0 hθl).1 hgt.le
    have hargl : (θl - c) / 2 - t = (θh - c) * (lam - τ) / 2 := by
      rw [hθl_eq]
      linarith
    have hEθl : TokenFinance.Debt.expect θl (fun x => TokenFinance.Debt.tokEnt c t x (TokenFinance.Debt.qm c x))
        = (lam - τ) ^ 3 / (1 - τ) ^ 3 * (θh / θl) * TokenFinance.Debt.npv c C0 θh := by
      rw [hTE, hargl, hcct]
      have hL3 : (θh - c) ^ 3 ≠ 0 := pow_ne_zero 3 hLne
      have h1t : (1 - τ) ^ 3 ≠ 0 := pow_ne_zero 3 (by linarith : (1 : ℝ) - τ ≠ 0)
      field_simp [hθhne, hθlne, hL3, h1t]
      ring
    constructor
    · intro hinc
      rw [hEθl, hEθh] at hinc
      linarith
    · intro h29
      rw [hEθl, hEθh]
      linarith
