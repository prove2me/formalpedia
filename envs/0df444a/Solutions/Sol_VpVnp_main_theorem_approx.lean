-- Prove2me | solution 1 for VpVnp.main_theorem_approx
-- status  : ACCEPTED   (prove)
-- author  : @Abhishek Anand
-- created : 2026-11-24T01:54:00.249957+00:00
-- url     : https://prove2.me/submissions/51a4ed2f-a576-4f8b-968c-a99c3d6c157e

import Theorems.Thm_ValiantBorder_allFields
import Mathlib
import Definitions.Def_VpVnp_Circuit
import Definitions.Def_VpVnp_Polynomials
import Definitions.Def_VpVnp_Beyond
import Definitions.Def_VpVnp_Approximates

open MvPolynomial

universe u

open VpVnp

theorem solution :
    ∃ c : ℝ, 0 < c ∧ ∀ p : ℕ, ∃ m₀ : ℕ, ∀ (F : Type u) [Field F] [CharP F p], ∀ m ≥ m₀, ∀ s : ℕ,
      (Approximates (hc F m) s → Beyond c m s) ∧ (p ≠ 2 → Approximates (perm F m) s → Beyond c m s) := by
  exact ValiantBorder.allFields.1
