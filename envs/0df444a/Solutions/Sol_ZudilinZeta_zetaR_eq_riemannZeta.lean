-- Prove2me | solution 1 for ZudilinZeta.zetaR_eq_riemannZeta
-- status  : ACCEPTED   (prove)
-- author  : @Yuxuan Xu
-- created : 2026-09-25T14:52:20.785117+00:00
-- url     : https://prove2.me/submissions/1fb31505-9ceb-4335-8a61-4c496d6d4514

import Mathlib
import Definitions.Def_ZudilinZetaSetup

/-!
# Solution of `ZudilinZeta.zetaR_eq_riemannZeta`

`theorem solution (k : ℕ) (hk : 2 ≤ k) : riemannZeta (k : ℂ) = (zetaR k : ℂ)`

Proof. For `k ≥ 2` Mathlib's identity
`zeta_eq_tsum_one_div_nat_add_one_cpow` gives

`riemannZeta (k : ℂ) = ∑' n : ℕ, 1 / (n + 1 : ℂ) ^ (k : ℂ)`,

and `Complex.cpow_natCast` turns `(n + 1 : ℂ) ^ (k : ℂ)` into `(n + 1 : ℂ) ^ k`.
On the other hand, by definition `zetaR k = ∑' n : ℕ, 1 / ((n : ℝ) + 1) ^ k`,
and `Complex.ofReal_tsum` moves the `ofReal` inside the series, so
`(zetaR k : ℂ) = ∑' n : ℕ, (1 : ℂ) / ((n : ℂ) + 1) ^ k`. These two series are
termwise equal. ∎
-/

open ZudilinZeta

theorem solution (k : ℕ) (hk : 2 ≤ k) : riemannZeta (k : ℂ) = (zetaR k : ℂ) := by
  have hk1 : 1 < (k : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le (by norm_num : (1 : ℕ) < 2) hk)
  have hre : 1 < (k : ℂ).re := by
    simpa using hk1
  rw [zeta_eq_tsum_one_div_nat_add_one_cpow (s := (k : ℂ)) hre]
  calc
    (∑' n : ℕ, 1 / (n + 1 : ℂ) ^ (k : ℂ)) = ∑' n : ℕ, (1 : ℂ) / ((n : ℂ) + 1) ^ k := by
      congr 1 with n
      rw [Complex.cpow_natCast]
    _ = (zetaR k : ℂ) := by
      simp [zetaR, Complex.ofReal_tsum]
