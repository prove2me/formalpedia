-- Prove2me | solution 1 for ValuationSubring.pairing_eq_one_of_inertia_smul_eq_nsmul_of_ne_two
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.503601+00:00
-- url     : https://prove2.me/submissions/88080e75-cf47-5442-94d6-f6ef08be77cf

import Mathlib
import Definitions.Def_FLTPrelim_Ramification
import Theorems.Thm_ValuationSubring_exists_mem_inertiaSubgroupIn_apply_eq_pow
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ValuationSubring_pairing_eq_one_of_inertia_smul_eq_nsmul_of_ne_two

set_option autoImplicit false

theorem solution
    {M : Type*} [AddCommGroup M] [DistribMulAction (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) M]
    (q : ℕ) [Fact q.Prime] (hq2 : q ≠ 2)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime q)
    (k : ℕ) (n : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) → ℕ)
    (hn : ∀ σ, ∀ ζ : AlgebraicClosure ℚ, ζ ^ (q ^ k) = 1 → σ ζ = ζ ^ n σ)
    (B : M → M → AlgebraicClosure ℚ)
    (W : Set M)
    (hWμ : ∀ x ∈ W, ∀ σ ∈ A.inertiaSubgroupIn ℚ, σ • x = n σ • x)
    (hWnsmul : ∀ x ∈ W, ∀ m : ℕ, m • x ∈ W)
    (hBval : ∀ x ∈ W, ∀ y ∈ W, B x y ^ (q ^ k) = 1)
    (hBl : ∀ x ∈ W, ∀ y ∈ W, ∀ m : ℕ, B (m • x) y = B x y ^ m)
    (hBr : ∀ x ∈ W, ∀ y ∈ W, ∀ m : ℕ, B x (m • y) = B x y ^ m)
    (hBgal : ∀ σ ∈ A.inertiaSubgroupIn ℚ, ∀ x ∈ W, ∀ y ∈ W, B (σ • x) (σ • y) = σ (B x y)) :
    ∀ x ∈ W, ∀ y ∈ W, B x y = 1 := by

  intro x hx y hy
  have hq : q.Prime := Fact.out
  have hbqk : B x y ^ (q ^ k) = 1 := hBval x hx y hy

  rcases Nat.eq_zero_or_pos k with hk0 | hkpos
  · rw [hk0, pow_zero, pow_one] at hbqk
    exact hbqk
  have hb0 : B x y ≠ 0 := by
    intro h0
    rw [h0, zero_pow (pow_ne_zero k hq.ne_zero)] at hbqk
    exact zero_ne_one hbqk

  have hcop : Nat.Coprime 2 q := (Nat.coprime_primes Nat.prime_two hq).mpr (Ne.symm hq2)
  obtain ⟨σ, hσI, hσ⟩ := ValuationSubring.exists_mem_inertiaSubgroupIn_apply_eq_pow A hq hA
    (ZMod.unitOfCoprime 2 hcop)
  have ha2 : ((ZMod.unitOfCoprime 2 hcop : (ZMod q)ˣ) : ZMod q).val = 2 := by
    rw [ZMod.coe_unitOfCoprime, ZMod.val_natCast]
    exact Nat.mod_eq_of_lt (lt_of_le_of_ne hq.two_le (Ne.symm hq2))

  haveI : NeZero ((q : ℕ) : AlgebraicClosure ℚ) := ⟨by exact_mod_cast hq.ne_zero⟩
  obtain ⟨ζ, hζ⟩ : ∃ ζ : AlgebraicClosure ℚ, IsPrimitiveRoot ζ q := by
    first
      | exact HasEnoughRootsOfUnity.exists_primitiveRoot (AlgebraicClosure ℚ) q
      | exact HasEnoughRootsOfUnity.prim
      | exact (HasEnoughRootsOfUnity.prim (R := AlgebraicClosure ℚ) (n := q))
  have hζ0 : ζ ≠ 0 := hζ.ne_zero hq.ne_zero
  obtain ⟨v, rfl⟩ : ∃ v : (AlgebraicClosure ℚ)ˣ, (v : AlgebraicClosure ℚ) = ζ := ⟨Units.mk0 ζ hζ0, rfl⟩
  have hζq : (v : AlgebraicClosure ℚ) ^ q = 1 := hζ.pow_eq_one
  have hζqk : (v : AlgebraicClosure ℚ) ^ (q ^ k) = 1 := by
    obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, (Nat.sub_add_cancel hkpos).symm⟩
    rw [pow_succ', pow_mul, hζq, one_pow]

  have hpowζ : (v : AlgebraicClosure ℚ) ^ n σ = (v : AlgebraicClosure ℚ) ^ 2 :=
    (hn σ _ hζqk).symm.trans
      ((hσ _ hζq).trans (congrArg (fun m : ℕ => (v : AlgebraicClosure ℚ) ^ m) ha2))
  have hmod : n σ ≡ 2 [MOD q] := by
    have hv : IsPrimitiveRoot v q := IsPrimitiveRoot.coe_units_iff.mp hζ
    have hpowv : v ^ n σ = v ^ 2 :=
      Units.ext (by rw [Units.val_pow_eq_pow_val, Units.val_pow_eq_pow_val]; exact hpowζ)
    rw [hv.eq_orderOf]
    exact pow_eq_pow_iff_modEq.mp hpowv

  have hσb : σ (B x y) = B x y ^ n σ := hn σ (B x y) hbqk
  have hny : n σ • y ∈ W := hWnsmul y hy (n σ)
  have hσb' : σ (B x y) = B x y ^ (n σ * n σ) := by

    have e1 := hBgal σ hσI x hx y hy
    rw [hWμ x hx σ hσI, hWμ y hy σ hσI, hBl x hx (n σ • y) hny (n σ), hBr x hx y hy (n σ),
      ← pow_mul] at e1
    exact e1.symm
  have hpow : B x y ^ n σ = B x y ^ (n σ * n σ) := hσb.symm.trans hσb'

  obtain ⟨u, hu⟩ : ∃ u : (AlgebraicClosure ℚ)ˣ, (u : AlgebraicClosure ℚ) = B x y := ⟨Units.mk0 _ hb0, rfl⟩
  have hupow : u ^ n σ = u ^ (n σ * n σ) :=
    Units.ext (by rw [Units.val_pow_eq_pow_val, Units.val_pow_eq_pow_val, hu]; exact hpow)
  have huqk : u ^ (q ^ k) = 1 :=
    Units.ext (by rw [Units.val_pow_eq_pow_val, hu, Units.val_one]; exact hbqk)
  have hord : orderOf u ∣ q ^ k := orderOf_dvd_of_pow_eq_one huqk
  obtain ⟨j, -, hjeq⟩ := (Nat.dvd_prime_pow hq).mp hord
  have hmodu : n σ ≡ n σ * n σ [MOD orderOf u] := pow_eq_pow_iff_modEq.mp hupow
  rcases Nat.eq_zero_or_pos j with hj0 | hjpos
  · rw [hj0, pow_zero] at hjeq
    have hu1 : u = 1 := orderOf_eq_one_iff.mp hjeq
    rw [← hu, hu1, Units.val_one]
  · exfalso
    rw [hjeq] at hmodu
    have hmodq : n σ ≡ n σ * n σ [MOD q] := Nat.ModEq.of_dvd (dvd_pow_self q hjpos.ne') hmodu

    have h24 : 2 ≡ 2 * 2 [MOD q] := hmod.symm.trans (hmodq.trans (Nat.ModEq.mul hmod hmod))
    have hqd : q ∣ 2 := by
      have := (Nat.modEq_iff_dvd' (by norm_num : 2 ≤ 2 * 2)).mp h24
      simpa using this
    exact hq2 ((Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).mp hqd)

end S_ValuationSubring_pairing_eq_one_of_inertia_smul_eq_nsmul_of_ne_two
end P2MW
export P2MW.S_ValuationSubring_pairing_eq_one_of_inertia_smul_eq_nsmul_of_ne_two (solution)
