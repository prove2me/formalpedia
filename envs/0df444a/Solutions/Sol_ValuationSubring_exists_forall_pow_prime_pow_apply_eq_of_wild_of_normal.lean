-- Prove2me | solution 1 for ValuationSubring.exists_forall_pow_prime_pow_apply_eq_of_wild_of_normal
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.503601+00:00
-- url     : https://prove2.me/submissions/da582f04-3ccc-5f92-8689-5352bb3e9cec

import Mathlib
import Definitions.Def_FLTPrelim_Ramification
import Theorems.Thm_ValuationSubring_apply_eq_self_of_pow_apply_eq_self_of_wild
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ValuationSubring_exists_forall_pow_prime_pow_apply_eq_of_wild_of_normal

set_option autoImplicit false

namespace P2mKcWildOrder

variable {K L : Type*} [Field K] [Field L] [Algebra K L]

theorem wild_mul (P : ValuationSubring L) {σ τ : L ≃ₐ[K] L}
    (hσ : ∀ z : L, z ≠ 0 → σ z * z⁻¹ - 1 ∈ P.nonunits)
    (hτ : ∀ z : L, z ≠ 0 → τ z * z⁻¹ - 1 ∈ P.nonunits) :
    ∀ z : L, z ≠ 0 → (σ * τ) z * z⁻¹ - 1 ∈ P.nonunits := by
  intro z hz
  have hτz : τ z ≠ 0 := by simpa using (τ.injective.ne hz)
  have h1 := hσ (τ z) hτz
  have h2 := hτ z hz

  have key : (σ * τ) z * z⁻¹ - 1 =
      (σ (τ z) * (τ z)⁻¹ - 1) * (τ z * z⁻¹ - 1) + (σ (τ z) * (τ z)⁻¹ - 1) + (τ z * z⁻¹ - 1) := by
    rw [AlgEquiv.mul_apply]
    field_simp
    ring
  rw [key]
  exact add_mem (add_mem (mul_mem h1 h2) h1) h2

theorem wild_pow (P : ValuationSubring L) {σ : L ≃ₐ[K] L}
    (hσ : ∀ z : L, z ≠ 0 → σ z * z⁻¹ - 1 ∈ P.nonunits) (n : ℕ) :
    ∀ z : L, z ≠ 0 → (σ ^ n) z * z⁻¹ - 1 ∈ P.nonunits := by
  induction n with
  | zero =>
      intro z hz
      simp [mul_inv_cancel₀ hz, zero_mem]
  | succ n ih =>
      rw [pow_succ]
      exact wild_mul P ih hσ

theorem pow_apply_eq_restrictNormal_pow (σ : L ≃ₐ[K] L) (F : IntermediateField K L) [Normal K F]
    (n : ℕ) (x : F) : (σ ^ n) (x : L) = (((σ.restrictNormal F) ^ n) x : F) := by
  induction n generalizing x with
  | zero => simp
  | succ n ih =>
      rw [pow_succ, pow_succ, AlgEquiv.mul_apply, AlgEquiv.mul_apply]
      have h := AlgEquiv.restrictNormal_commutes σ F x

      change ((σ.restrictNormal F x : F) : L) = σ (x : L) at h
      rw [← h, ih]

end P2mKcWildOrder

open P2mKcWildOrder in
theorem solution
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    {p : ℕ} (hp : p.Prime) (P : ValuationSubring L) (hP : P.LiesOverPrime p)
    {σ : L ≃ₐ[K] L} (hwild : ∀ z : L, z ≠ 0 → σ z * z⁻¹ - 1 ∈ P.nonunits)
    (F : IntermediateField K L) [FiniteDimensional K F] [Normal K F] :
    ∃ a : ℕ, ∀ x ∈ F, (σ ^ (p ^ a)) x = x := by
  classical
  let σF : F ≃ₐ[K] F := σ.restrictNormal F

  have hfin : IsOfFinOrder σF := isOfFinOrder_of_finite σF
  set N := orderOf σF with hNdef
  have hN : N ≠ 0 := (IsOfFinOrder.orderOf_pos hfin).ne'
  obtain ⟨a, m, hm, hNam⟩ := Nat.exists_eq_pow_mul_and_not_dvd hN p hp.ne_one
  refine ⟨a, fun x hx => ?_⟩

  have hρ : ∀ z : L, z ≠ 0 → (σ ^ (p ^ a)) z * z⁻¹ - 1 ∈ P.nonunits := wild_pow P hwild (p ^ a)
  have hfix : ((σ ^ (p ^ a)) ^ m) x = x := by
    rw [← pow_mul, ← hNam]
    have h := pow_apply_eq_restrictNormal_pow σ F N ⟨x, hx⟩
    rw [hNdef, pow_orderOf_eq_one] at h
    simpa using h
  have hcop : m.Coprime p := (Nat.Prime.coprime_iff_not_dvd hp).mpr hm |>.symm
  exact ValuationSubring.apply_eq_self_of_pow_apply_eq_self_of_wild P hP hρ hcop hfix

end S_ValuationSubring_exists_forall_pow_prime_pow_apply_eq_of_wild_of_normal
end P2MW
export P2MW.S_ValuationSubring_exists_forall_pow_prime_pow_apply_eq_of_wild_of_normal (solution)
