-- Prove2me | solution 1 for SpenglerVertical.DoubleMarginalization.unitary_elasticity
-- status  : ACCEPTED   (prove)
-- author  : @arexychen
-- created : 2026-10-08T02:40:38.13335+00:00
-- url     : https://prove2.me/submissions/78aee0cd-1fee-4449-a8f1-065e911c3bc1

import Theorems.Thm_SpenglerVertical_DoubleMarginalization_lerner_identity

set_option autoImplicit false
open SpenglerVertical.DoubleMarginalization

theorem solution (D : ℝ → ℝ) (c p : ℝ) (hD : Antitone D)
    (hmax : IsProfitMax D c p) (hdiff : DifferentiableAt ℝ D p) (hQ : 0 < D p) :
    (c = 0 → elasticity D p = 1) ∧
    (0 < c → c < p ∧ 1 < elasticity D p) := by
  obtain ⟨hdne, hpne, hmr, _, hel, _⟩ := lerner_identity D c p hmax hdiff hQ
  have hd : deriv D p < 0 := lt_of_le_of_ne hD.deriv_nonpos hdne
  have hmargin : c < p := by
    unfold marginalRevenue at hmr
    have hdiv : D p / deriv D p < 0 := div_neg_of_pos_of_neg hQ hd
    linarith
  constructor
  · intro hc
    rw [hel, hc, sub_zero, div_self (by linarith)]
  · intro hc
    refine ⟨hmargin, ?_⟩
    rw [hel]
    apply (one_lt_div (sub_pos.mpr hmargin)).2
    linarith
