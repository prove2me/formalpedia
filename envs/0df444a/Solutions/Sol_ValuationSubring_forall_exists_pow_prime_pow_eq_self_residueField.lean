-- Prove2me | solution 1 for ValuationSubring.forall_exists_pow_prime_pow_eq_self_residueField
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.503601+00:00
-- url     : https://prove2.me/submissions/92e54612-2766-5e20-b6df-2cf260d7f7be

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ValuationSubring_forall_exists_pow_prime_pow_eq_self_residueField

set_option autoImplicit false

theorem exists_pow_prime_pow_eq_self_of_aeval_int_eq_zero {k : Type*} [Field k] (p : ℕ) [Fact p.Prime] [CharP k p]
    (x : k) (f : Polynomial ℤ) (hf : Polynomial.map (Int.castRingHom (ZMod p)) f ≠ 0) (hfx : Polynomial.aeval x f = 0) :
    ∃ n : ℕ, 0 < n ∧ x ^ p ^ n = x := by
  classical
  letI : Algebra (ZMod p) k := ZMod.algebra k p

  have halg : IsAlgebraic (ZMod p) x := by
    refine ⟨Polynomial.map (Int.castRingHom (ZMod p)) f, hf, ?_⟩
    rw [show Int.castRingHom (ZMod p) = algebraMap ℤ (ZMod p) from (algebraMap_int_eq (ZMod p)).symm,
      Polynomial.aeval_map_algebraMap]
    exact hfx
  have hint : IsIntegral (ZMod p) x := halg.isIntegral

  let F := IntermediateField.adjoin (ZMod p) ({x} : Set k)
  haveI : FiniteDimensional (ZMod p) F := IntermediateField.adjoin.finiteDimensional hint
  haveI : Finite F := Module.finite_of_finite (ZMod p)
  letI : Fintype F := Fintype.ofFinite F
  haveI : CharP F p := by
    have := (algebraMap F k).charP_iff_charP p
    exact this.mpr inferInstance
  obtain ⟨n, hp', hcard⟩ := FiniteField.card F p
  refine ⟨(n : ℕ), n.pos, ?_⟩
  have hxF : x ∈ F := IntermediateField.subset_adjoin _ _ (Set.mem_singleton x)
  have key := FiniteField.pow_card (⟨x, hxF⟩ : F)
  rw [hcard] at key
  have := congrArg (fun y : F => (y : k)) key
  simpa using this

theorem solution
    {L : Type*} [Field L] [CharZero L] [Algebra ℚ L] [Algebra.IsAlgebraic ℚ L] (A : ValuationSubring L)
    (p : ℕ) [Fact p.Prime] [CharP (IsLocalRing.ResidueField ↥A) p] :
    ∀ x : IsLocalRing.ResidueField ↥A, ∃ n : ℕ, 0 < n ∧ x ^ p ^ n = x := by
  classical
  intro x
  obtain ⟨a, rfl⟩ := IsLocalRing.residue_surjective x

  have haQ : IsAlgebraic ℚ (a : L) := Algebra.IsAlgebraic.isAlgebraic _
  have haZ : IsAlgebraic ℤ (a : L) := (IsFractionRing.isAlgebraic_iff ℤ ℚ L).mpr haQ
  obtain ⟨f₀, hf₀, hf₀a⟩ := haZ
  set f := f₀.primPart with hfdef
  have hfprim : f.IsPrimitive := f₀.isPrimitive_primPart
  have hfa : Polynomial.aeval (a : L) f = 0 := by
    have h := hf₀a
    rw [f₀.eq_C_content_mul_primPart, map_mul, Polynomial.aeval_C] at h
    rcases mul_eq_zero.mp h with h | h
    · rw [eq_intCast, Int.cast_eq_zero] at h
      exact absurd h (fun hc => hf₀ (Polynomial.content_eq_zero_iff.mp hc))
    · exact h

  have hfaA : Polynomial.aeval a f = 0 := by
    apply Subtype.val_injective

    have : ((Polynomial.aeval a f : ↥A) : L) = Polynomial.aeval (a : L) f := by
      rw [show ((a : ↥A) : L) = algebraMap (↥A) L a from rfl, Polynomial.aeval_algebraMap_apply]
      rfl
    rw [this, hfa]; rfl
  have hfx : Polynomial.aeval (IsLocalRing.residue ↥A a) f = 0 := by
    have h1 : Polynomial.aeval (IsLocalRing.residue ↥A a) f = IsLocalRing.residue ↥A (Polynomial.aeval a f) :=
      Polynomial.aeval_algHom_apply ((IsLocalRing.residue ↥A).toIntAlgHom) a f
    rw [h1, hfaA, map_zero]

  have hfbar : Polynomial.map (Int.castRingHom (ZMod p)) f ≠ 0 := by
    intro h0
    apply (Nat.Prime.ne_one Fact.out : p ≠ 1)
    have hdvd : ∀ i, (p : ℤ) ∣ f.coeff i := fun i => by
      have := congrArg (fun g => Polynomial.coeff g i) h0
      simp only [Polynomial.coeff_map, Int.coe_castRingHom, Polynomial.coeff_zero] at this
      exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mp this
    have h1 : IsUnit ((p : ℤ)) := hfprim (p : ℤ) ((Polynomial.C_dvd_iff_dvd_coeff _ _).mpr hdvd)
    rcases Int.isUnit_iff.mp h1 with h | h
    · exact_mod_cast h
    · exact absurd h (by have := (Fact.out : p.Prime).pos; omega)
  exact exists_pow_prime_pow_eq_self_of_aeval_int_eq_zero p _ f hfbar hfx

end S_ValuationSubring_forall_exists_pow_prime_pow_eq_self_residueField
end P2MW
export P2MW.S_ValuationSubring_forall_exists_pow_prime_pow_eq_self_residueField (solution)
