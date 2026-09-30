-- Prove2me | solution 1 for SP4ArtinTwist.same_parity_S5_period
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-08T02:03:25.350979+00:00
-- url     : https://prove2.me/submissions/f16a8c96-a63d-481d-af8b-50cb1e99251c

import Definitions.Def_SP4ArtinTwist
import Mathlib.GroupTheory.Perm.Sign
import Mathlib.Tactic

set_option autoImplicit false

namespace SP4ArtinTwist

private theorem fullTwist_apply {G : Type*} [Group G] (a b : G) :
    fullTwist G (a, b) =
      ((a * b) * a * (a * b)⁻¹, (a * b) * b * (a * b)⁻¹) := by
  change artin G (artin G (a, b)) = _
  apply Prod.ext <;> (dsimp [artin]; group)

private theorem artin_product {G : Type*} [Group G] (a b : G) :
    (artin G (a, b)).1 * (artin G (a, b)).2 = a * b := by
  dsimp [artin]
  group

private theorem fullTwist_pow_apply {G : Type*} [Group G] (a b : G) (m : ℕ) :
    (fullTwist G ^ m) (a, b) =
      ((a * b)^m * a * ((a * b)^m)⁻¹, (a * b)^m * b * ((a * b)^m)⁻¹) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [pow_succ', Equiv.Perm.mul_apply, ih, fullTwist_apply]
    have hprod : ((a * b)^m * a * ((a * b)^m)⁻¹) *
        ((a * b)^m * b * ((a * b)^m)⁻¹) = a * b := by
      calc
        _ = (a * b)^m * (a * b) * ((a * b)^m)⁻¹ := by group
        _ = a * b := by
          rw [← pow_succ, pow_succ', mul_assoc, mul_inv_cancel, mul_one]
    rw [hprod]
    apply Prod.ext <;> dsimp <;> rw [pow_succ'] <;> simp [mul_inv_rev, mul_assoc]

private theorem period_of_product_pow {G : Type*} [Group G] (a b : G)
    (N : ℕ) (hN : (a * b)^N = 1) (n : ℤ) :
    (fullTwist G ^ (n + (N : ℤ))) (a, b) = (fullTwist G ^ n) (a, b) := by
  rw [zpow_add, zpow_natCast, Equiv.Perm.mul_apply, fullTwist_pow_apply, hN]
  simp

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem even_S5_pow_thirty :
    ∀ g : Equiv.Perm (Fin 5), Equiv.Perm.sign g = 1 → g ^ (30 : ℕ) = 1 := by
  decide

end SP4ArtinTwist

open SP4ArtinTwist

/-- The finite local algebra only: no knot group, representation gluing,
cover-count bijection, or geometric application is part of this statement. -/
theorem solution (a b : Equiv.Perm (Fin 5))
    (hparity : Equiv.Perm.sign a = Equiv.Perm.sign b) :
    (a * b) ^ (30 : ℕ) = 1 ∧
    (∀ m : ℕ, (fullTwist (Equiv.Perm (Fin 5)) ^ m) (a, b) =
      ((a * b)^m * a * ((a * b)^m)⁻¹, (a * b)^m * b * ((a * b)^m)⁻¹)) ∧
    (∀ n : ℤ, (fullTwist (Equiv.Perm (Fin 5)) ^ (n + 30)) (a, b) =
      (fullTwist (Equiv.Perm (Fin 5)) ^ n) (a, b)) := by
  have hsign : Equiv.Perm.sign (a * b) = 1 := by
    rw [map_mul, hparity, Int.units_mul_self]
  have hN := even_S5_pow_thirty (a * b) hsign
  refine ⟨hN, fullTwist_pow_apply a b, ?_⟩
  intro n
  exact period_of_product_pow a b 30 hN n
