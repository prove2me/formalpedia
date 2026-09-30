-- Prove2me | solution 1 for TranscendenceTheory.finite_quotient_multiplicity_model
-- status  : ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-09-21T01:06:47.22687+00:00
-- url     : https://prove2.me/submissions/38f14e06-0cd7-4a9f-adb7-a06345997c25

import Definitions.Def_TranscendenceTheory_FiniteAlgebraMultiplicityModel
import Mathlib.RingTheory.Localization.Ideal
import Mathlib.RingTheory.Localization.Submodule
import Mathlib.RingTheory.Ideal.Quotient.Operations

noncomputable section

namespace TranscendenceTheory

theorem ringEquiv_self_length_eq {R S : Type*} [CommRing R] [CommRing S]
    (e : R ≃+* S) : Module.length R R = Module.length S S := by
  let f : R →ₛₗ[e.toRingHom] S :=
    { toFun := e
      map_add' := e.map_add
      map_smul' := fun a b => e.map_mul a b }
  let : RingHomSurjective e.toRingHom := ⟨e.surjective⟩
  rw [Module.length, Module.length, WithBot.unbot_inj]
  exact Order.krullDim_eq_of_orderIso
    (Submodule.orderIsoMapComapOfBijective f e.bijective)

theorem quotient_localization_length_eq
    (R : Type*) [CommRing R] (I p : Ideal R) [p.IsPrime] (hIp : I ≤ p) :
    let q := p.map (Ideal.Quotient.mk I)
    letI : q.IsPrime := Ideal.isPrime_map_quotientMk_of_isPrime hIp
    Module.length (Localization.AtPrime p)
      ((Localization.AtPrime p) ⧸ I.map (algebraMap R (Localization.AtPrime p))) =
      Module.length (Localization.AtPrime q) (Localization.AtPrime q) := by
  let q := p.map (Ideal.Quotient.mk I)
  let : q.IsPrime := Ideal.isPrime_map_quotientMk_of_isPrime hIp
  let : q.LiesOver p := ⟨(Ideal.comap_map_mk hIp).symm⟩
  have hcompl : Algebra.algebraMapSubmonoid (R ⧸ I) p.primeCompl = q.primeCompl :=
    Ideal.algebraMapSubmonoid_primeCompl_of_liesOver_surjective q p Ideal.Quotient.mk_surjective
  let Rp := Localization.AtPrime p
  let J := I.map (algebraMap R Rp)
  let : IsLocalization (Algebra.algebraMapSubmonoid (R ⧸ I) p.primeCompl)
      (Localization.AtPrime q) := by
    rw [hcompl]
    infer_instance
  let e := IsLocalization.algEquiv (Algebra.algebraMapSubmonoid (R ⧸ I) p.primeCompl)
    (Rp ⧸ J) (Localization.AtPrime q)
  exact (Module.length_eq_of_surjective (S := Rp) (R := Rp ⧸ J) (M := Rp ⧸ J)
    Ideal.Quotient.mk_surjective).trans (ringEquiv_self_length_eq e.toRingEquiv)

end TranscendenceTheory

open TranscendenceTheory

theorem solution
    (R : Type) [CommRing R] [Algebra ℂ R] (I : Ideal R)
    [Module.Finite ℂ (R ⧸ I)] (ι : Type) (p : ι → PrimeSpectrum R)
    (hp : Function.Injective p) (hIp : ∀ i, I ≤ (p i).asIdeal) :
    ∃ M : FiniteAlgebraMultiplicityModel ι,
      Module.finrank ℂ M.A = Module.finrank ℂ (R ⧸ I) ∧
      ∀ i, M.localLength i =
        (Module.length (Localization.AtPrime (p i).asIdeal)
          ((Localization.AtPrime (p i).asIdeal) ⧸ I.map
            (algebraMap R (Localization.AtPrime (p i).asIdeal)))).toNat ∧
        Module.length (Localization.AtPrime (p i).asIdeal)
          ((Localization.AtPrime (p i).asIdeal) ⧸ I.map
            (algebraMap R (Localization.AtPrime (p i).asIdeal))) ≠ ⊤ := by
  let q : ι → PrimeSpectrum (R ⧸ I) := fun i =>
    ⟨(p i).asIdeal.map (Ideal.Quotient.mk I),
      Ideal.isPrime_map_quotientMk_of_isPrime (hIp i)⟩
  have hq : Function.Injective q := by
    intro i j h
    apply hp
    apply PrimeSpectrum.ext
    have he := congrArg (fun t : PrimeSpectrum (R ⧸ I) =>
      t.asIdeal.comap (Ideal.Quotient.mk I)) h
    simpa only [q, Ideal.comap_map_mk (hIp i), Ideal.comap_map_mk (hIp j)] using he
  let M : FiniteAlgebraMultiplicityModel ι :=
    { A := R ⧸ I
      point := q
      point_injective := hq }
  refine ⟨M, rfl, ?_⟩
  intro i
  have he := quotient_localization_length_eq R I (p i).asIdeal (hIp i)
  refine ⟨?_, ?_⟩
  · exact congrArg ENat.toNat he.symm
  · rw [he]
    let : IsArtinianRing (R ⧸ I) := IsArtinianRing.of_finite ℂ _
    let : IsNoetherianRing (R ⧸ I) := isNoetherian_of_tower ℂ inferInstance
    exact Module.length_ne_top
