-- Prove2me | solution 1 for VpVnp.main_theorem
-- status  : ACCEPTED   (prove)
-- author  : @Abhishek Anand
-- created : 2026-11-24T01:53:58.928548+00:00
-- url     : https://prove2.me/submissions/06f58a73-435f-4c9b-89c9-b8fb407cbc75

import Theorems.Thm_ValiantBorder_exactLowerBound
import Mathlib
import Definitions.Def_VpVnp_Circuit
import Definitions.Def_VpVnp_Polynomials
import Definitions.Def_VpVnp_Beyond

open MvPolynomial

universe u

open VpVnp

theorem solution :
    ∃ c : ℝ, 0 < c ∧ ∀ p : ℕ, ∃ m₀ : ℕ, ∀ (F : Type u) [Field F] [CharP F p], ∀ m ≥ m₀, ∀ s : ℕ,
      (Computes (hc F m) s → Beyond c m s) ∧ (p ≠ 2 → Computes (perm F m) s → Beyond c m s) := by
  exact ValiantBorder.exactLowerBound
