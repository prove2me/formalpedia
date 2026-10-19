-- Prove2me | solution 1 for TokenFinance.MoralHazard.proposition_5
-- status  : ACCEPTED   (prove)
-- author  : @mihalyimark
-- created : 2026-10-19T11:32:19.460579+00:00
-- url     : https://prove2.me/submissions/0f539a28-b745-402d-8522-aca3759371dc

/-
DS19D proof of the MoralHazard milestone TokenFinance.MoralHazard.proposition_5
(theorem_id ab183d96-a9d6-47ae-ac34-65c8025403e5), p. 28, equation (20).

Mathematics.  For a uniform demand intercept on (0,θ), the monopoly profit is
π^m(x) = max(x−c,0)²/4, hence E_θ[π^m] = (θ−c)³/(12θ).  The equity share is
α_s = C₀/E_{θh}[π^m], so the entrepreneur's effort payoff under equity is
(1−α_s)E_{θh}[π^m] − C_e = NPV_h − C_e, while her no-effort payoff is
(1−α_s)E_{θl}[π^m] = (E_{θl}[π^m]/E_{θh}[π^m])·NPV_h
= λ³(θh/θl)·NPV_h with λ=(θl−c)/(θh−c).  Comparing the two gives (20).

The file is standalone: it imports only Mathlib and the two platform definition
modules used by the live target signature.
-/
import Mathlib
import Definitions.Def_TokenFinance_Debt_Setting
import Definitions.Def_TokenFinance_MoralHazard_Financeable

private lemma expect_pim (c θ : ℝ) (hc : 0 < c) (hcθ : c < θ) :
    TokenFinance.Debt.expect θ (TokenFinance.Debt.pim c) = (θ - c) ^ 3 / (12 * θ) := by
  have hθ : 0 < θ := lt_trans hc hcθ
  have hθne : θ ≠ 0 := ne_of_gt hθ
  have hc0 : 0 ≤ c := le_of_lt hc
  have hzeroAux : ∀ x ∈ Set.uIcc (0 : ℝ) c, TokenFinance.Debt.pim c x = 0 := by
    intro x hx
    rw [Set.uIcc_of_le hc0] at hx
    have hx' : x ≤ c := hx.2
    unfold TokenFinance.Debt.pim
    rw [max_eq_right (by linarith)]
    ring
  have hzero : ∫ x in (0 : ℝ)..c, TokenFinance.Debt.pim c x = 0 := by
    rw [intervalIntegral.integral_congr hzeroAux]
    exact intervalIntegral.integral_zero
  have hcong : ∀ x ∈ Set.uIcc c θ, TokenFinance.Debt.pim c x = (x - c) ^ 2 / 4 := by
    intro x hx
    rw [Set.uIcc_of_le hcθ.le] at hx
    have hge : 0 ≤ x - c := by linarith [hx.1]
    unfold TokenFinance.Debt.pim
    rw [max_eq_left hge]
  have hFcont : Continuous fun x : ℝ => (x - c) ^ 2 / 4 := by fun_prop
  have hderiv : ∀ y : ℝ, HasDerivAt (fun z : ℝ => (z - c) ^ 3 / 12)
      ((y - c) ^ 2 / 4) y := by
    intro y
    have h1 : HasDerivAt (fun z : ℝ => (z - c) ^ 3)
        ((3 : ℕ) * (y - c) ^ ((3 : ℕ) - 1) * 1) y :=
      (hasDerivAt_id y).sub_const c |>.pow 3
    have hval : (3 : ℕ) * (y - c) ^ ((3 : ℕ) - 1) * 1 / 12 = (y - c) ^ 2 / 4 := by
      norm_num
      ring
    rw [show (y - c) ^ 2 / 4 = (3 : ℕ) * (y - c) ^ ((3 : ℕ) - 1) * 1 / 12 by
      rw [hval]]
    exact h1.div_const 12
  have hcalc : ∫ x in c..θ, (x - c) ^ 2 / 4 = (θ - c) ^ 3 / 12 := by
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun y _ => hderiv y)
      (hFcont.intervalIntegrable _ _)]
    ring
  have hpimcont : Continuous fun x : ℝ => TokenFinance.Debt.pim c x := by
    unfold TokenFinance.Debt.pim
    fun_prop
  have hsplit : (∫ x in (0 : ℝ)..c, TokenFinance.Debt.pim c x)
      + (∫ x in c..θ, TokenFinance.Debt.pim c x)
      = ∫ x in (0 : ℝ)..θ, TokenFinance.Debt.pim c x :=
    intervalIntegral.integral_add_adjacent_intervals
      (hpimcont.intervalIntegrable 0 c) (hpimcont.intervalIntegrable c θ)
  unfold TokenFinance.Debt.expect
  rw [show (∫ x in (0 : ℝ)..θ, TokenFinance.Debt.pim c x)
      = ∫ x in c..θ, TokenFinance.Debt.pim c x by
    rw [← hsplit, hzero, zero_add]]
  rw [intervalIntegral.integral_congr hcong, hcalc]
  field_simp [hθne]

theorem solution (c C0 Ce θl θh lam : ℝ) (hc : 0 < c) (hcl : c < θl) (hlh : θl < θh)
    (hC0 : 0 < C0) (hnpv : 0 < TokenFinance.Debt.npv c C0 θh)
    (hlam : lam = (θl - c) / (θh - c)) :
    TokenFinance.MoralHazard.EquityFinanceable c C0 Ce θl θh ↔
      TokenFinance.Debt.npv c C0 θh - Ce ≥
        lam ^ 3 * (θh / θl) * TokenFinance.Debt.npv c C0 θh := by
  have hcθh : c < θh := lt_trans hcl hlh
  have hθh : 0 < θh := lt_trans hc hcθh
  have hθl : 0 < θl := lt_trans hc hcl
  have hLh : 0 < θh - c := by linarith
  have hLl : 0 < θl - c := by linarith
  have hAh : TokenFinance.Debt.expect θh (TokenFinance.Debt.pim c)
      = (θh - c) ^ 3 / (12 * θh) := expect_pim c θh hc hcθh
  have hAl : TokenFinance.Debt.expect θl (TokenFinance.Debt.pim c)
      = (θl - c) ^ 3 / (12 * θl) := expect_pim c θl hc hcl
  have hApos : 0 < TokenFinance.Debt.expect θh (TokenFinance.Debt.pim c) := by
    rw [hAh]
    positivity
  have hAne : TokenFinance.Debt.expect θh (TokenFinance.Debt.pim c) ≠ 0 := ne_of_gt hApos
  have hnpv : TokenFinance.Debt.npv c C0 θh
      = TokenFinance.Debt.expect θh (TokenFinance.Debt.pim c) - C0 := rfl
  have hratio : (1 - TokenFinance.Debt.equityShare c C0 θh)
        * TokenFinance.Debt.expect θh (TokenFinance.Debt.pim c)
      = TokenFinance.Debt.npv c C0 θh := by
    unfold TokenFinance.Debt.equityShare TokenFinance.Debt.npv
    field_simp [hAne]
  have hratio_l : (1 - TokenFinance.Debt.equityShare c C0 θh)
        * TokenFinance.Debt.expect θl (TokenFinance.Debt.pim c)
      = lam ^ 3 * (θh / θl) * TokenFinance.Debt.npv c C0 θh := by
    have hB : TokenFinance.Debt.expect θl (TokenFinance.Debt.pim c)
        = (θl - c) ^ 3 / (12 * θl) := hAl
    have hA : TokenFinance.Debt.expect θh (TokenFinance.Debt.pim c)
        = (θh - c) ^ 3 / (12 * θh) := hAh
    unfold TokenFinance.Debt.equityShare TokenFinance.Debt.npv
    rw [hA, hB, hlam]
    field_simp [ne_of_gt hθh, ne_of_gt hθl, ne_of_gt hLh]
  unfold TokenFinance.MoralHazard.EquityFinanceable
  rw [hratio, hratio_l]
