-- Prove2me | solution 1 for ValuationSubring.nonempty_residueField_ringEquiv_algebraicClosure_zmod_of_liesOverPrime
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.503601+00:00
-- url     : https://prove2.me/submissions/ac408456-7eff-507f-92e7-3a1e4253e698

import Mathlib
import Definitions.Def_FLTPrelim_Ramification
import Theorems.Thm_ValuationSubring_exists_integral_mul_eq_of_liesOverPrime
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ValuationSubring_nonempty_residueField_ringEquiv_algebraicClosure_zmod_of_liesOverPrime

set_option autoImplicit false

open Polynomial

theorem solution
    (A : ValuationSubring (AlgebraicClosure ℚ)) {q : ℕ} [Fact q.Prime] (hA : A.LiesOverPrime q) :
    Nonempty (IsLocalRing.ResidueField A ≃+* AlgebraicClosure (ZMod q)) := by
  classical
  have hq : q.Prime := Fact.out

  have hqmax : ((q : ℕ) : A) ∈ IsLocalRing.maximalIdeal A := by
    rw [ValuationSubring.valuation_lt_one_iff]
    exact (A.mem_nonunits_iff).mp (by simp at hA ⊢; exact hA)
  have hq0 : ((q : ℕ) : IsLocalRing.ResidueField A) = 0 := by
    have h := (IsLocalRing.residue_eq_zero_iff ((q : ℕ) : A)).mpr hqmax
    simpa using h
  haveI : CharP (IsLocalRing.ResidueField A) q := (CharP.charP_iff_prime_eq_zero hq).mpr hq0

  letI : Algebra (ZMod q) (IsLocalRing.ResidueField A) := ZMod.algebra _ q
  have hres : Function.Surjective (IsLocalRing.residue A) := Ideal.Quotient.mk_surjective

  have hint : ∀ {x : AlgebraicClosure ℚ}, IsIntegral A x → x ∈ A := fun {x} hx => by
    obtain ⟨y, rfl⟩ := (IsIntegrallyClosed.isIntegral_iff (K := AlgebraicClosure ℚ)).mp hx
    exact y.2

  have hintZ : ∀ z : integralClosure ℤ (AlgebraicClosure ℚ), (z : AlgebraicClosure ℚ) ∈ A := fun z => by
    obtain ⟨P, hPmon, hPz⟩ := z.2
    refine hint ⟨P.map (Int.castRingHom A), hPmon.map _, ?_⟩
    rw [Polynomial.eval₂_map,
      show (algebraMap A (AlgebraicClosure ℚ)).comp (Int.castRingHom A) = algebraMap ℤ (AlgebraicClosure ℚ) from
        RingHom.ext_int _ _]
    exact hPz

  haveI : IsAlgClosed (IsLocalRing.ResidueField A) := by
    refine IsAlgClosed.of_exists_root _ fun p hp hirr => ?_
    have hlifts : p ∈ Polynomial.lifts (IsLocalRing.residue A) := by
      rw [Polynomial.mem_lifts]
      exact Polynomial.map_surjective _ hres p
    obtain ⟨P, hPmap, hPdeg, hPmon⟩ := Polynomial.lifts_and_natDegree_eq_and_monic hlifts hp
    have hdeg : (P.map (algebraMap A (AlgebraicClosure ℚ))).degree ≠ 0 := by
      rw [hPmon.degree_map, Polynomial.degree_eq_natDegree hPmon.ne_zero, hPdeg]
      exact_mod_cast (Polynomial.natDegree_pos_iff_degree_pos.mpr
        (Polynomial.degree_pos_of_irreducible hirr)).ne'
    obtain ⟨α, hα⟩ := IsAlgClosed.exists_root _ hdeg
    have hαint : IsIntegral A α := ⟨P, hPmon, by rwa [Polynomial.IsRoot.def, Polynomial.eval_map] at hα⟩
    obtain ⟨a, rfl⟩ : ∃ a : A, (a : AlgebraicClosure ℚ) = α := ⟨⟨α, hint hαint⟩, rfl⟩
    have hPa : P.eval a = 0 := by
      rw [Polynomial.IsRoot.def, Polynomial.eval_map,
        show (a : AlgebraicClosure ℚ) = algebraMap A (AlgebraicClosure ℚ) a from rfl,
        Polynomial.eval₂_hom] at hα
      change ((P.eval a : A) : AlgebraicClosure ℚ) = 0 at hα
      exact_mod_cast hα
    refine ⟨IsLocalRing.residue A a, ?_⟩
    rw [← hPmap, Polynomial.eval_map, Polynomial.eval₂_hom, hPa, map_zero]

  have halg : ∀ (z : integralClosure ℤ (AlgebraicClosure ℚ)) (hz : (z : AlgebraicClosure ℚ) ∈ A),
      IsAlgebraic (ZMod q) (IsLocalRing.residue A ⟨z, hz⟩) := by
    intro z hz
    obtain ⟨P, hPmon, hPz⟩ := z.2
    refine ⟨P.map (Int.castRingHom (ZMod q)), (hPmon.map _).ne_zero, ?_⟩
    rw [Polynomial.aeval_def, Polynomial.eval₂_map,
      show (algebraMap (ZMod q) (IsLocalRing.ResidueField A)).comp (Int.castRingHom (ZMod q)) =
        algebraMap ℤ (IsLocalRing.ResidueField A) from RingHom.ext_int _ _,
      ← Polynomial.aeval_def,
      show IsLocalRing.residue A ⟨z, hz⟩ = (IsLocalRing.residue A).toIntAlgHom ⟨z, hz⟩ from rfl,
      Polynomial.aeval_algHom_apply]
    have h0 : Polynomial.aeval (⟨z, hz⟩ : A) P = 0 := by
      have h1 : algebraMap A (AlgebraicClosure ℚ) (Polynomial.aeval (⟨z, hz⟩ : A) P) =
          P.eval₂ (algebraMap ℤ (AlgebraicClosure ℚ)) (z : AlgebraicClosure ℚ) := by
        rw [Polynomial.aeval_def, Polynomial.hom_eval₂,
          RingHom.ext_int ((algebraMap A (AlgebraicClosure ℚ)).comp (algebraMap ℤ A))
            (algebraMap ℤ (AlgebraicClosure ℚ))]
        rfl
      have h' : ((Polynomial.aeval (⟨z, hz⟩ : A) P : A) : AlgebraicClosure ℚ) = 0 := h1.trans hPz
      exact_mod_cast h'
    rw [h0, map_zero]
  haveI : Algebra.IsAlgebraic (ZMod q) (IsLocalRing.ResidueField A) := by
    refine ⟨fun x => ?_⟩
    obtain ⟨a, rfl⟩ := hres x
    obtain ⟨y, s, hs, hys⟩ := A.exists_integral_mul_eq_of_liesOverPrime hq hA a a.2
    have hsA : (s : AlgebraicClosure ℚ) ∈ A := hintZ s
    have hyA : (y : AlgebraicClosure ℚ) ∈ A := hintZ y
    have hmul : a * ⟨s, hsA⟩ = ⟨y, hyA⟩ := Subtype.ext hys
    have hs0 : IsLocalRing.residue A ⟨s, hsA⟩ ≠ 0 := by
      rw [Ne, IsLocalRing.residue_eq_zero_iff, ValuationSubring.valuation_lt_one_iff, ← A.mem_nonunits_iff]
      exact hs
    have hx : IsLocalRing.residue A a =
        IsLocalRing.residue A ⟨y, hyA⟩ * (IsLocalRing.residue A ⟨s, hsA⟩)⁻¹ := by
      rw [eq_mul_inv_iff_mul_eq₀ hs0, ← map_mul, hmul]
    rw [hx]
    exact (halg y hyA).mul (halg s hsA).inv

  haveI : IsAlgClosure (ZMod q) (IsLocalRing.ResidueField A) := ⟨inferInstance, inferInstance⟩
  exact ⟨(IsAlgClosure.equiv (ZMod q) (IsLocalRing.ResidueField A) (AlgebraicClosure (ZMod q))).toRingEquiv⟩

end S_ValuationSubring_nonempty_residueField_ringEquiv_algebraicClosure_zmod_of_liesOverPrime
end P2MW
export P2MW.S_ValuationSubring_nonempty_residueField_ringEquiv_algebraicClosure_zmod_of_liesOverPrime (solution)
