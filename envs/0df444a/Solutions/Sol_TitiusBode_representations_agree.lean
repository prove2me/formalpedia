-- Prove2me | solution 1 for TitiusBode.representations_agree
-- status  : ACCEPTED   (prove)
-- author  : @Gabewhigham
-- created : 2026-10-10T19:32:31.231903+00:00
-- url     : https://prove2.me/submissions/01d16692-ce12-44e7-aa59-6985c11cc23e

import Definitions.Def_TitiusBode_Defs
import Mathlib
open Filter Topology
open TitiusBode

theorem solution :
    ((tbOriginal 0 : ℝ) = tbTenths ⊥ ∧
      ∀ n : ℕ, (tbOriginal (n + 1) : ℝ) = tbTenths (n : WithBot ℕ)) ∧
    (∀ n : WithBot ℕ, tbAU n = tbTenths n / 10) ∧
    (∀ n : ℕ, tbAU (n : WithBot ℕ) = tbCanonical n) := by
  have hX : ∀ n : ℕ, tbX (n + 1) = 3 * 2 ^ n := by
    intro n
    induction n with
    | zero => rfl
    | succ k ih => rw [tbX, ih]; ring
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
  · norm_num [tbOriginal, tbX, tbTenths, twoPowExt]
  · intro n
    simp only [tbOriginal, hX, tbTenths, twoPowExt]
    push_cast; ring
  · intro n
    cases n with
    | bot => norm_num [tbAU, tbTenths, twoPowExt]
    | coe k => simp only [tbAU, tbTenths, twoPowExt]; ring
  · intro n
    simp [tbAU, tbCanonical, twoPowExt]
