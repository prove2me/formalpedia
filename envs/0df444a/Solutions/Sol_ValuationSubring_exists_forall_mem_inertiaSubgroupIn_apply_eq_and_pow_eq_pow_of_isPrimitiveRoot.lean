-- Prove2me | solution 1 for ValuationSubring.exists_forall_mem_inertiaSubgroupIn_apply_eq_and_pow_eq_pow_of_isPrimitiveRoot
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.503601+00:00
-- url     : https://prove2.me/submissions/5a022a8e-822e-52db-b476-355d094bcb54

import Mathlib
import Definitions.Def_FLTPrelim_Ramification
import Theorems.Thm_ValuationSubring_exists_mem_inertiaSubgroupIn_apply_eq_pow_of_pow_prime_pow_eq_one
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ValuationSubring_exists_forall_mem_inertiaSubgroupIn_apply_eq_and_pow_eq_pow_of_isPrimitiveRoot

set_option autoImplicit false

namespace KummerDescent

variable {K L : Type*} [Field K] [Field L] [Algebra K L]

lemma exists_forall_apply_eq_pow {n : ℕ} (hn : 0 < n) {ζ : L} (hζ : IsPrimitiveRoot ζ n) (σ : L ≃ₐ[K] L) :
    ∃ a : ℕ, ∀ η : L, η ^ n = 1 → σ η = η ^ a := by
  haveI : NeZero n := ⟨hn.ne'⟩
  have h1 : (σ ζ) ^ n = 1 := by rw [← map_pow, hζ.pow_eq_one, map_one]
  obtain ⟨a, -, ha⟩ := hζ.eq_pow_of_pow_eq_one h1
  refine ⟨a, fun η hη => ?_⟩
  obtain ⟨b, -, rfl⟩ := hζ.eq_pow_of_pow_eq_one hη
  rw [map_pow, ← ha, ← pow_mul, ← pow_mul, mul_comm]

theorem exists_forall_apply_eq_and_pow_eq_pow {n : ℕ} (hn : 0 < n) (I : Subgroup (L ≃ₐ[K] L)) {ζ : L}
    (hζ : IsPrimitiveRoot ζ n) (g₀ : L ≃ₐ[K] L) (hg₀ : g₀ ∈ I) (hg₀act : ∀ η : L, η ^ n = 1 → g₀ η = η ^ 2)
    (w : L) (hw : ∀ σ ∈ I, σ ζ = ζ → σ w = w) (hx : ∀ σ ∈ I, σ (w ^ n) = w ^ n) :
    ∃ w' : L, (∀ σ ∈ I, σ w' = w') ∧ w' ^ n = w ^ n := by
  by_cases hw0 : w = 0
  · exact ⟨0, fun σ _ => map_zero σ, by rw [hw0]⟩

  let η : (L ≃ₐ[K] L) → L := fun σ => σ w / w
  have hηw : ∀ σ : L ≃ₐ[K] L, σ w = η σ * w := fun σ => by
    change σ w = σ w / w * w
    rw [div_mul_cancel₀ _ hw0]
  have hηn : ∀ σ ∈ I, η σ ^ n = 1 := fun σ hσ => by
    change (σ w / w) ^ n = 1
    rw [div_pow, ← map_pow, hx σ hσ, div_self (pow_ne_zero _ hw0)]
  have hη0 : ∀ σ ∈ I, η σ ≠ 0 := fun σ hσ h => by
    have h1 := hηn σ hσ
    rw [h, zero_pow hn.ne'] at h1
    exact zero_ne_one h1

  have key : ∀ σ ∈ I, σ (η g₀) = η σ * η g₀ := by
    intro σ hσ
    obtain ⟨a, ha⟩ := exists_forall_apply_eq_pow hn hζ σ
    have hζa : (ζ ^ a) ^ n = 1 := by rw [← pow_mul, mul_comm, pow_mul, hζ.pow_eq_one, one_pow]

    have hL : (σ * g₀) ζ = ζ ^ (2 * a) := by
      rw [AlgEquiv.mul_apply, hg₀act ζ hζ.pow_eq_one, map_pow, ha ζ hζ.pow_eq_one, ← pow_mul, mul_comm]
    have hR : (g₀ * σ) ζ = ζ ^ (2 * a) := by
      rw [AlgEquiv.mul_apply, ha ζ hζ.pow_eq_one, hg₀act _ hζa, ← pow_mul, mul_comm]

    have hdI : (g₀ * σ)⁻¹ * (σ * g₀) ∈ I :=
      I.mul_mem (I.inv_mem (I.mul_mem hg₀ hσ)) (I.mul_mem hσ hg₀)
    have hdζ : ((g₀ * σ)⁻¹ * (σ * g₀)) ζ = ζ := by
      rw [AlgEquiv.mul_apply, hL, ← hR, ← AlgEquiv.mul_apply, inv_mul_cancel, AlgEquiv.one_apply]
    have hdw := hw _ hdI hdζ
    have hcommw : (σ * g₀) w = (g₀ * σ) w := by
      have h2 := congrArg (g₀ * σ) hdw
      rwa [← AlgEquiv.mul_apply, ← mul_assoc, mul_inv_cancel, one_mul] at h2
    have hL' : (σ * g₀) w = σ (η g₀) * η σ * w := by
      rw [AlgEquiv.mul_apply, hηw g₀, map_mul, hηw σ, mul_assoc]
    have hR' : (g₀ * σ) w = η σ ^ 2 * η g₀ * w := by
      rw [AlgEquiv.mul_apply, hηw σ, map_mul, hg₀act _ (hηn σ hσ), hηw g₀, mul_assoc]
    rw [hL', hR'] at hcommw
    have h3 : σ (η g₀) * η σ = η σ ^ 2 * η g₀ := mul_right_cancel₀ hw0 hcommw
    apply mul_right_cancel₀ (hη0 σ hσ)
    rw [h3]
    ring
  refine ⟨w / η g₀, fun σ hσ => ?_, ?_⟩
  · rw [map_div₀, key σ hσ, hηw σ, mul_comm (η σ) w, mul_comm (η σ) (η g₀), mul_div_mul_right _ _ (hη0 σ hσ)]
  · rw [div_pow, hηn g₀ hg₀, div_one]

end KummerDescent

theorem solution
    (p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) (N : ℕ) (P : ValuationSubring (AlgebraicClosure ℚ)) (hP : P.LiesOverPrime p)
    (ζ : AlgebraicClosure ℚ) (hζ : IsPrimitiveRoot ζ (p ^ N)) (w : AlgebraicClosure ℚ)
    (hw : ∀ σ ∈ P.inertiaSubgroupIn ℚ, σ ζ = ζ → σ w = w)
    (hx : ∀ σ ∈ P.inertiaSubgroupIn ℚ, σ (w ^ p ^ N) = w ^ p ^ N) :
    ∃ w' : AlgebraicClosure ℚ, (∀ σ ∈ P.inertiaSubgroupIn ℚ, σ w' = w') ∧ w' ^ p ^ N = w ^ p ^ N := by
  have hn : 0 < p ^ N := pow_pos hp.pos N
  have h2 : Nat.Coprime 2 (p ^ N) :=
    ((Nat.coprime_primes Nat.prime_two hp).mpr (Ne.symm hp2)).pow_right N
  obtain ⟨g₀, hg₀, hg₀act⟩ :=
    ValuationSubring.exists_mem_inertiaSubgroupIn_apply_eq_pow_of_pow_prime_pow_eq_one P hp hP N
      (ZMod.unitOfCoprime 2 h2)
  refine KummerDescent.exists_forall_apply_eq_and_pow_eq_pow hn (P.inertiaSubgroupIn ℚ) hζ g₀ hg₀ ?_ w hw hx
  intro η hη
  have hmod : η ^ (2 % p ^ N) = η ^ 2 := by
    conv_rhs => rw [← Nat.div_add_mod 2 (p ^ N), pow_add, pow_mul, hη, one_pow, one_mul]
  have hthis := hg₀act η hη
  rw [ZMod.coe_unitOfCoprime, ZMod.val_natCast, hmod] at hthis
  convert hthis using 1

end S_ValuationSubring_exists_forall_mem_inertiaSubgroupIn_apply_eq_and_pow_eq_pow_of_isPrimitiveRoot
end P2MW
export P2MW.S_ValuationSubring_exists_forall_mem_inertiaSubgroupIn_apply_eq_and_pow_eq_pow_of_isPrimitiveRoot (solution)
