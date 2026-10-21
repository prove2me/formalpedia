-- Prove2me | solution 1 for WeilConjectures.projectiveLine_zeta
-- status  : ACCEPTED   (prove)
-- author  : @Idealson
-- created : 2026-10-20T08:10:41.471825+00:00
-- url     : https://prove2.me/submissions/0ad308f8-131f-433c-8dfc-0a12c7fcddb7

import Mathlib
import Definitions.Def_WeilConjectures_projectiveSpace
import Definitions.Def_WeilConjectures_zetaFunction
import Theorems.Thm_WeilConjectures_projectiveSpace_zeta

/-!
# `projectiveLine_zeta` : le cas `n = 1` de `projectiveSpace_zeta`

`N_m = q⁰ʼᵐ + q¹ʼᵐ = 1 + q^m` et `∏_{i ≤ 1} (1 - qⁱ T) = (1 - T)(1 - qT)`.
-/

open AlgebraicGeometry CategoryTheory Polynomial
open WeilConjectures

theorem solution (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [Finite k] [CharP k p] :
    (∀ m : ℕ, 1 ≤ m → pointCount p (projectiveSpace.toSpec k 1) m = Nat.card k ^ m + 1) ∧
    zetaFunction p (projectiveSpace.toSpec k 1) *
      ((1 - PowerSeries.X) * (1 - PowerSeries.C (Nat.card k : ℚ) * PowerSeries.X)) = 1 := by
  obtain ⟨hN, hZ⟩ := projectiveSpace_zeta p k 1
  refine ⟨fun m hm ↦ ?_, ?_⟩
  · rw [hN m hm, Finset.sum_range_succ, Finset.sum_range_one]
    ring
  · rw [Finset.prod_range_succ, Finset.prod_range_one] at hZ
    simpa using hZ
