-- Prove2me | solution 1 for WeierstrassCurve.exists_valuationSubring_with_transcendental_of_charZero
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.822295+00:00
-- url     : https://prove2.me/submissions/7340c7e8-71fc-5a87-9862-c7abd8cfdbed

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_WeierstrassCurve_exists_valuationSubring_with_transcendental_of_charZero

set_option autoImplicit false

open Polynomial WeierstrassCurve

namespace D0Aux

theorem isLocalHom_powerSeriesC (R : Type*) [CommRing R] : IsLocalHom (PowerSeries.C (R := R)) := by
  refine ⟨fun a ha => ?_⟩
  rwa [PowerSeries.isUnit_iff_constantCoeff, PowerSeries.constantCoeff_C] at ha

theorem powerSeriesC_injective (R : Type*) [CommRing R] : Function.Injective (PowerSeries.C (R := R)) :=
  Function.LeftInverse.injective (g := PowerSeries.constantCoeff) fun a => PowerSeries.constantCoeff_C a

theorem eval₂_C_X_powerSeries {R : Type*} [CommRing R] (P : Polynomial R) :
    P.eval₂ (PowerSeries.C (R := R)) PowerSeries.X = (P : PowerSeries R) := by
  have h : Polynomial.eval₂RingHom (PowerSeries.C (R := R)) PowerSeries.X =
      Polynomial.coeToPowerSeries.ringHom := by
    refine Polynomial.ringHom_ext (fun a => ?_) ?_
    · rw [Polynomial.coe_eval₂RingHom, Polynomial.eval₂_C]
      exact (Polynomial.coe_C a).symm
    · rw [Polynomial.coe_eval₂RingHom, Polynomial.eval₂_X]
      exact Polynomial.coe_X.symm
  exact congrArg (fun φ : Polynomial R →+* PowerSeries R => φ P) h

end D0Aux

universe u

set_option maxHeartbeats 12800000 in
set_option synthInstance.maxHeartbeats 1600000 in
theorem solution
    (k : Type u) [Field k] [CharZero k] :
    ∃ (L : Type u) (_ : Field L) (_ : IsAlgClosed L) (_ : CharZero L)
      (A : ValuationSubring L) (φ : k →+* L) (hφ : ∀ x, φ x ∈ A)
      (ι : k →+* IsLocalRing.ResidueField A),
      (∀ a : k, IsLocalRing.residue A ⟨φ a, hφ a⟩ = ι a) ∧
      ∃ (t : L) (ht : t ∈ A), (⟨t, ht⟩ : A) ∈ IsLocalRing.maximalIdeal A ∧
        ∀ P : Polynomial k, P ≠ 0 → P.eval₂ φ t ≠ 0 := by
  classical
  haveI hR'0 : CharZero (PowerSeries k) :=
    charZero_of_injective_ringHom (f := PowerSeries.C (R := k)) (D0Aux.powerSeriesC_injective _)
  haveI : CharZero (FractionRing (PowerSeries k)) := IsFractionRing.charZero (PowerSeries k)
  haveI hL : CharZero (AlgebraicClosure (FractionRing (PowerSeries k))) :=
    charZero_of_injective_algebraMap (algebraMap (FractionRing (PowerSeries k)) _).injective
  let ψ : PowerSeries k →+* AlgebraicClosure (FractionRing (PowerSeries k)) :=
    (algebraMap (FractionRing (PowerSeries k)) _).comp (algebraMap (PowerSeries k) (FractionRing (PowerSeries k)))
  have hψ : Function.Injective ψ :=
    (algebraMap (FractionRing (PowerSeries k)) _).injective.comp (IsFractionRing.injective (PowerSeries k) _)
  obtain ⟨A, hAmem, hAloc⟩ := IsLocalRing.exists_factor_valuationRing ψ
  let g : PowerSeries k →+* A := ψ.codRestrict A.toSubring hAmem
  haveI : IsLocalHom g := hAloc
  let φ : k →+* AlgebraicClosure (FractionRing (PowerSeries k)) := ψ.comp (PowerSeries.C (R := k))
  have hφ : ∀ x, φ x ∈ A := fun x => hAmem _
  refine ⟨AlgebraicClosure (FractionRing (PowerSeries k)), inferInstance, inferInstance, hL,
    A, φ, hφ, (IsLocalRing.residue A).comp (g.comp (PowerSeries.C (R := k))), fun a => rfl,
    ψ PowerSeries.X, hAmem _, ?_, ?_⟩
  · rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    intro hu
    have hX : IsUnit (PowerSeries.X : PowerSeries k) := IsUnit.of_map g _ hu
    rw [PowerSeries.isUnit_iff_constantCoeff, PowerSeries.constantCoeff_X] at hX
    exact not_isUnit_zero hX
  · intro P hP h0
    apply hP
    rw [show P.eval₂ φ (ψ PowerSeries.X) = ψ (P.eval₂ (PowerSeries.C (R := k)) PowerSeries.X)
      from (Polynomial.hom_eval₂ P _ ψ PowerSeries.X).symm, D0Aux.eval₂_C_X_powerSeries] at h0
    exact Polynomial.coe_eq_zero_iff.mp (hψ (by rw [h0, map_zero]))

end S_WeierstrassCurve_exists_valuationSubring_with_transcendental_of_charZero
end P2MW
export P2MW.S_WeierstrassCurve_exists_valuationSubring_with_transcendental_of_charZero (solution)
