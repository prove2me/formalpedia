-- Prove2me | solution 1 for WittVector.exists_valuationSubring_lift_with_transcendental
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:14.293936+00:00
-- url     : https://prove2.me/submissions/878024c4-f319-5fe8-97e0-caf4f6ff3c21

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_WittVector_exists_valuationSubring_lift_with_transcendental

set_option autoImplicit false

namespace WittLift

open WittVector IsLocalRing

section Witt
variable (p : ℕ) [hp : Fact p.Prime] (k : Type*) [Field k] [CharP k p] [PerfectRing k p]

omit [CharP k p] [PerfectRing k p] in
theorem coeff_zero_natCast (m : ℕ) : ((m : WittVector p k)).coeff 0 = (m : k) := by
  rw [← WittVector.constantCoeff_apply, map_natCast]

private theorem _root_.WittLift.charZero : CharZero (WittVector p k) := by
  haveI : IsDomain (WittVector p k) := inferInstance
  refine charZero_of_inj_zero fun n hn => ?_
  by_contra hn0
  obtain ⟨a, m, hm, rfl⟩ := Nat.exists_eq_pow_mul_and_not_dvd hn0 p hp.out.ne_one
  have hmunit : IsUnit ((m : ℕ) : WittVector p k) := by
    apply isUnit_of_coeff_zero_ne_zero
    rw [coeff_zero_natCast]
    intro h0
    exact hm ((CharP.cast_eq_zero_iff k p m).mp h0)
  have hp0 : ((p : WittVector p k)) ≠ 0 := fun h => by
    have h1 := congrArg (fun x : WittVector p k => x.coeff 1) h
    simp only [WittVector.coeff_p_one, WittVector.zero_coeff] at h1
    exact one_ne_zero h1
  have hpa : ((p ^ a : ℕ) : WittVector p k) ≠ 0 := by
    rw [Nat.cast_pow]
    exact pow_ne_zero _ hp0
  rw [Nat.cast_mul] at hn
  exact hpa ((hmunit.mul_left_eq_zero).mp hn)

p2m_export "WittLift" "charZero"
omit [PerfectRing k p] in

theorem not_isUnit_p : ¬ IsUnit ((p : WittVector p k)) := by
  intro hu
  have h0 : WittVector.constantCoeff ((p : WittVector p k)) = (0 : k) := by
    rw [map_natCast, CharP.cast_eq_zero]
  have := hu.map (WittVector.constantCoeff : WittVector p k →+* k)
  rw [h0] at this
  exact not_isUnit_zero this

noncomputable def residueMap {A : Type*} [CommRing A] [IsLocalRing A] (f : WittVector p k →+* A) [IsLocalHom f] :
    k →+* ResidueField A :=
  (RingHom.liftOfRightInverse (WittVector.constantCoeff : WittVector p k →+* k) (WittVector.teichmuller p)
    (fun a => by rw [WittVector.constantCoeff_apply, WittVector.teichmuller_coeff_zero]))
    ⟨(residue A).comp f, by
      rw [WittVector.ker_constantCoeff, Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe,
        RingHom.mem_ker, RingHom.comp_apply, residue_eq_zero_iff, mem_maximalIdeal, mem_nonunits_iff]
      exact fun hu => not_isUnit_p p k (IsUnit.of_map f _ hu)⟩

theorem residueMap_constantCoeff {A : Type*} [CommRing A] [IsLocalRing A] (f : WittVector p k →+* A)
    [IsLocalHom f] (x : WittVector p k) :
    residueMap p k f (WittVector.constantCoeff x) = residue A (f x) :=
  RingHom.liftOfRightInverse_comp_apply _ _ _ _ x

theorem residueMap_comp_teichmuller {A : Type*} [CommRing A] [IsLocalRing A] (f : WittVector p k →+* A)
    [IsLocalHom f] (a : k) :
    residueMap p k f a = residue A (f (WittVector.teichmuller p a)) := by
  conv_lhs => rw [show a = WittVector.constantCoeff (WittVector.teichmuller p a) by
    rw [WittVector.constantCoeff_apply, WittVector.teichmuller_coeff_zero]]
  exact residueMap_constantCoeff p k f _

end Witt

end WittLift

namespace WittLift

open WittVector IsLocalRing

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

end WittLift

universe u

set_option maxHeartbeats 12800000 in
set_option synthInstance.maxHeartbeats 1600000 in
theorem solution
    (p : ℕ) [Fact p.Prime] (K : Type u) [Field K] [CharP K p] [PerfectRing K p] :
    ∃ (L : Type u) (_ : Field L) (_ : IsAlgClosed L) (_ : CharZero L)
      (A : ValuationSubring L) (φ : WittVector p K →+* L) (hφ : ∀ x, φ x ∈ A)
      (ι : K →+* IsLocalRing.ResidueField A),
      (∀ a : K, IsLocalRing.residue A ⟨φ (WittVector.teichmuller p a), hφ _⟩ = ι a) ∧
      ∃ (t : L) (ht : t ∈ A), (⟨t, ht⟩ : A) ∈ IsLocalRing.maximalIdeal A ∧
        ∀ P : Polynomial (WittVector p K), P ≠ 0 → P.eval₂ φ t ≠ 0 := by
  classical
  haveI hW0 : CharZero (WittVector p K) := WittLift.charZero p K
  haveI hR'0 : CharZero (PowerSeries (WittVector p K)) :=
    charZero_of_injective_ringHom (f := PowerSeries.C (R := WittVector p K))
      (WittLift.powerSeriesC_injective _)
  haveI : CharZero (FractionRing (PowerSeries (WittVector p K))) :=
    IsFractionRing.charZero (PowerSeries (WittVector p K))
  haveI hL : CharZero (AlgebraicClosure (FractionRing (PowerSeries (WittVector p K)))) :=
    charZero_of_injective_algebraMap
      (algebraMap (FractionRing (PowerSeries (WittVector p K))) _).injective

  let ψ : PowerSeries (WittVector p K) →+* AlgebraicClosure (FractionRing (PowerSeries (WittVector p K))) :=
    (algebraMap (FractionRing (PowerSeries (WittVector p K))) _).comp
      (algebraMap (PowerSeries (WittVector p K)) (FractionRing (PowerSeries (WittVector p K))))
  have hψ : Function.Injective ψ :=
    (algebraMap (FractionRing (PowerSeries (WittVector p K))) _).injective.comp
      (IsFractionRing.injective (PowerSeries (WittVector p K)) _)

  obtain ⟨A, hAmem, hAloc⟩ := IsLocalRing.exists_factor_valuationRing ψ
  let g : PowerSeries (WittVector p K) →+* A := ψ.codRestrict A.toSubring hAmem
  haveI : IsLocalHom g := hAloc
  haveI := WittLift.isLocalHom_powerSeriesC (WittVector p K)
  let f : WittVector p K →+* A := g.comp (PowerSeries.C (R := WittVector p K))
  haveI : IsLocalHom f := RingHom.isLocalHom_comp g _
  let φ : WittVector p K →+* AlgebraicClosure (FractionRing (PowerSeries (WittVector p K))) :=
    ψ.comp (PowerSeries.C (R := WittVector p K))
  have hφ : ∀ x, φ x ∈ A := fun x => hAmem _
  refine ⟨AlgebraicClosure (FractionRing (PowerSeries (WittVector p K))), inferInstance, inferInstance, hL,
    A, φ, hφ, WittLift.residueMap p K f, fun a => ?_, ψ PowerSeries.X, hAmem _, ?_, ?_⟩
  ·
    exact (WittLift.residueMap_comp_teichmuller p K f a).symm
  ·
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    intro hu
    have hX : IsUnit (PowerSeries.X : PowerSeries (WittVector p K)) := IsUnit.of_map g _ hu
    rw [PowerSeries.isUnit_iff_constantCoeff, PowerSeries.constantCoeff_X] at hX
    exact not_isUnit_zero hX
  ·
    intro P hP h0
    apply hP
    rw [show P.eval₂ φ (ψ PowerSeries.X) = ψ (P.eval₂ (PowerSeries.C (R := WittVector p K)) PowerSeries.X)
      from (Polynomial.hom_eval₂ P _ ψ PowerSeries.X).symm, WittLift.eval₂_C_X_powerSeries] at h0
    exact Polynomial.coe_eq_zero_iff.mp (hψ (by rw [h0, map_zero]))

end S_WittVector_exists_valuationSubring_lift_with_transcendental
end P2MW
export P2MW.S_WittVector_exists_valuationSubring_lift_with_transcendental (solution)
