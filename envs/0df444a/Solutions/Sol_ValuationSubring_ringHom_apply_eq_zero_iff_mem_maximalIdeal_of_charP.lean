-- Prove2me | solution 1 for ValuationSubring.ringHom_apply_eq_zero_iff_mem_maximalIdeal_of_charP
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.503601+00:00
-- url     : https://prove2.me/submissions/3c51a0b4-ee76-5cc8-a298-d3eeae689ff2

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ValuationSubring_ringHom_apply_eq_zero_iff_mem_maximalIdeal_of_charP
set_option autoImplicit false

namespace HKer

open Polynomial

theorem exists_isPrimitive_aeval_eq_zero (c : AlgebraicClosure ℚ) :
    ∃ p : ℤ[X], p.IsPrimitive ∧ aeval c p = 0 := by
  obtain ⟨p, hp, hpc⟩ := (AlgebraicClosure.isAlgebraic ℚ).isAlgebraic c
  set p' : ℤ[X] := IsLocalization.integerNormalization (nonZeroDivisors ℤ) p with hp'def
  have hp' : p' ≠ 0 := fun h => hp ((IsFractionRing.integerNormalization_eq_zero_iff).mp h)
  have hpc' : aeval c p' = 0 := IsLocalization.integerNormalization_aeval_eq_zero (nonZeroDivisors ℤ) p hpc
  refine ⟨p'.primPart, p'.isPrimitive_primPart, ?_⟩
  rw [p'.eq_C_content_mul_primPart, map_mul, aeval_C] at hpc'
  rcases mul_eq_zero.mp hpc' with h | h
  · exfalso
    rw [map_eq_zero_iff _ (algebraMap ℤ (AlgebraicClosure ℚ)).injective_int, content_eq_zero_iff] at h
    exact hp' h
  · exact h

theorem map_ne_zero_of_isPrimitive {p : ℤ[X]} (hp : p.IsPrimitive) (q : ℕ) [Fact q.Prime] :
    p.map (Int.castRingHom (ZMod q)) ≠ 0 := by
  intro h
  have hdvd : (C (q : ℤ)) ∣ p := by
    rw [C_dvd_iff_dvd_coeff]
    intro n
    have hn : (p.map (Int.castRingHom (ZMod q))).coeff n = 0 := by rw [h, coeff_zero]
    rw [coeff_map, eq_intCast, ZMod.intCast_zmod_eq_zero_iff_dvd] at hn
    exact hn
  have := hp (q : ℤ) hdvd
  rw [Int.isUnit_iff_natAbs_eq, Int.natAbs_natCast] at this
  exact (Fact.out : q.Prime).one_lt.ne' this

section
variable (A : ValuationSubring (AlgebraicClosure ℚ)) {k : Type*} [Field k]

theorem isMaximal_ker (q : ℕ) [Fact q.Prime] [CharP k q] (red : A →+* k) : (RingHom.ker red).IsMaximal := by
  set 𝔭 := RingHom.ker red
  haveI : 𝔭.IsPrime := RingHom.ker_isPrime red
  have hι : Function.Injective (RingHom.kerLift red) := RingHom.kerLift_injective red
  haveI : CharP (A ⧸ 𝔭) q := RingHom.charP (RingHom.kerLift red) hι q
  letI : Algebra (ZMod q) (A ⧸ 𝔭) := ZMod.algebra _ q

  haveI : Algebra.IsIntegral (ZMod q) (A ⧸ 𝔭) := by
    refine ⟨fun x => ?_⟩
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
    obtain ⟨p, hprim, hpa⟩ := exists_isPrimitive_aeval_eq_zero (a : AlgebraicClosure ℚ)

    have key : (A.subtype : A →+* AlgebraicClosure ℚ) (aeval a p) = aeval (a : AlgebraicClosure ℚ) (p.map (RingHom.id ℤ)) :=
      map_aeval_eq_aeval_map (RingHom.ext_int _ _) p a
    rw [Polynomial.map_id, hpa] at key
    have hpaA : aeval a p = 0 := Subtype.val_injective (by simpa using key)

    have hpq : aeval (Ideal.Quotient.mk 𝔭 a) (p.map (Int.castRingHom (ZMod q))) = 0 := by
      have := map_aeval_eq_aeval_map (φ := Int.castRingHom (ZMod q)) (ψ := Ideal.Quotient.mk 𝔭) (RingHom.ext_int _ _) p a
      rw [← this, hpaA, map_zero]
    exact (isAlgebraic_iff_isIntegral).mp ⟨_, map_ne_zero_of_isPrimitive hprim q, hpq⟩
  have hF : IsField (A ⧸ 𝔭) := isField_of_isIntegral_of_isField' (R := ZMod q) (Field.toIsField (ZMod q))
  exact Ideal.Quotient.maximal_of_isField _ hF

theorem ker_eq_maximalIdeal (q : ℕ) [Fact q.Prime] [CharP k q] (red : A →+* k) :
    RingHom.ker red = IsLocalRing.maximalIdeal A :=
  IsLocalRing.eq_maximalIdeal (isMaximal_ker A q red)

end

end HKer

theorem solution
    (A : ValuationSubring (AlgebraicClosure ℚ)) {k : Type*} [Field k] (q : ℕ) [Fact q.Prime] [CharP k q]
    (red : A →+* k) (c : A) :
    red c = 0 ↔ c ∈ IsLocalRing.maximalIdeal A := by
  rw [← HKer.ker_eq_maximalIdeal A q red, RingHom.mem_ker]

end S_ValuationSubring_ringHom_apply_eq_zero_iff_mem_maximalIdeal_of_charP
end P2MW
export P2MW.S_ValuationSubring_ringHom_apply_eq_zero_iff_mem_maximalIdeal_of_charP (solution)
