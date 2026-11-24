-- Prove2me | solution 1 for ValiantBorder.closedLaurentLowerBound
-- status  : ACCEPTED   (prove)
-- author  : @Abhishek Anand
-- created : 2026-11-24T00:18:58.028319+00:00
-- url     : https://prove2.me/submissions/8c1cf04f-9f04-4daf-8c4f-5ac404bbce65

/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import Theorems.Thm_ValiantBorder_gridProjections
import Theorems.Thm_ValiantBorder_gridLaurentRate

/-! Adapted from Claude (Anthropic), *VP ≠ VNP over every field*, Appendix M and the sections
on grids. Source: `anthropics/formal-math` revision 11b6c7e3c927df2658f513b6b68ea7f8929c62c5,
`vp-vnp/Nc/PermValiant.lean`, `Nc/Rate/Defs.lean`, `Nc/Perm{Coeff,Grid,Sum,Pad}.lean`,
`Nc/Hc/{Grid,Segments}.lean` and `Paper/{Grids,HcGrid}.lean`, Apache-2.0. -/
theorem solution (K : Type) [Field K] [IsAlgClosed K] :
    ∃ m₀ : ℕ, ∀ m ≥ m₀, ∀ (s : ℕ) (Q : MvPolynomial (Fin m × Fin m) (LaurentPolynomial K)),
      Statement.Computes Q s →
      ((∀ d, (∀ i : ℤ, i < 0 → (MvPolynomial.coeff d Q).coeff i = 0) ∧
          (MvPolynomial.coeff d Q).coeff 0 = MvPolynomial.coeff d (Statement.hc K m)) →
        (2 : ℝ) ^ ((Real.logb 2 m) ^ (4 / 3 : ℝ) / 1600 ^ 2) < s) ∧
      ((2 : K) ≠ 0 → (∀ d, (∀ i : ℤ, i < 0 → (MvPolynomial.coeff d Q).coeff i = 0) ∧
          (MvPolynomial.coeff d Q).coeff 0 = MvPolynomial.coeff d (Statement.perm K m)) →
        (2 : ℝ) ^ ((Real.logb 2 m) ^ (4 / 3 : ℝ) / 1600 ^ 2) < s)  := by
  obtain ⟨hHC, hPERM⟩ := ValiantBorder.gridProjections K
  obtain ⟨M₁, h₁⟩ := ValiantBorder.gridLaurentRate hHC
  by_cases htwo : (2 : K) = 0
  · exact ⟨M₁, fun m hm s Q hQ => ⟨h₁ m hm s Q hQ, fun hn => (hn htwo).elim⟩⟩
  · obtain ⟨M₂, h₂⟩ := ValiantBorder.gridLaurentRate (hPERM htwo)
    exact ⟨M₁ + M₂, fun m hm s Q hQ => ⟨h₁ m (by omega) s Q hQ, fun _ => h₂ m (by omega) s Q hQ⟩⟩
