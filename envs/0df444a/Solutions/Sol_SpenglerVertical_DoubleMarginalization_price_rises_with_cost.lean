-- Prove2me | solution 1 for SpenglerVertical.DoubleMarginalization.price_rises_with_cost
-- status  : ACCEPTED   (prove)
-- author  : @arexychen
-- created : 2026-10-08T02:40:36.446794+00:00
-- url     : https://prove2.me/submissions/3b5c5cc6-8027-4479-b52f-b77b12454924

import Definitions.Def_SpenglerVertical_DoubleMarginalization_Model

set_option autoImplicit false
open SpenglerVertical.DoubleMarginalization

private theorem profit_first_order (D : ℝ → ℝ) (c p : ℝ)
    (hmax : IsProfitMax D c p) (hdiff : DifferentiableAt ℝ D p) :
    D p + (p - c) * deriv D p = 0 := by
  have hlocal : IsLocalMax (profit D c) p := Filter.Eventually.of_forall hmax
  have hd : HasDerivAt (profit D c) (D p + (p - c) * deriv D p) p := by
    unfold profit
    convert ((hasDerivAt_id p).sub_const c).mul hdiff.hasDerivAt using 1 <;> first | rfl | (simp only [id_eq]; ring) | ring
  exact hlocal.hasDerivAt_eq_zero hd

theorem solution (D : ℝ → ℝ) (c₁ c₂ p₁ p₂ : ℝ) (hc : c₁ < c₂)
    (h₁ : IsProfitMax D c₁ p₁) (h₂ : IsProfitMax D c₂ p₂) :
    D p₂ ≤ D p₁ ∧
    (Antitone D → 0 < D p₂ → p₁ ≤ p₂) ∧
    (Antitone D → 0 < D p₂ → DifferentiableAt ℝ D p₂ → p₁ < p₂) := by
  have h12 := h₁ p₂
  have h21 := h₂ p₁
  unfold profit at h12 h21
  have hquant : D p₂ ≤ D p₁ := by nlinarith
  have hprice : Antitone D → 0 < D p₂ → p₁ ≤ p₂ := by
    intro hD hQ
    by_contra hn
    have hp : p₂ < p₁ := lt_of_not_ge hn
    have hqeq : D p₁ = D p₂ := le_antisymm (hD (le_of_lt hp)) hquant
    rw [hqeq] at h21
    nlinarith
  refine ⟨hquant, hprice, ?_⟩
  intro hD hQ hdiff
  apply lt_of_le_of_ne (hprice hD hQ)
  intro heq
  subst p₁
  have hf1 := profit_first_order D c₁ p₂ h₁ hdiff
  have hf2 := profit_first_order D c₂ p₂ h₂ hdiff
  have hd : deriv D p₂ = 0 := by nlinarith
  rw [hd] at hf1
  nlinarith
