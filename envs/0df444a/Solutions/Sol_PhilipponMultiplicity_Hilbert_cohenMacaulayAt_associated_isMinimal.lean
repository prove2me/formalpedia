-- Prove2me | solution 1 for PhilipponMultiplicity.Hilbert.cohenMacaulayAt_associated_isMinimal
-- status  : ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-09-26T05:23:28.066158+00:00
-- url     : https://prove2.me/submissions/7a666190-1789-4587-9503-6e5451699a75

import Definitions.Def_PhilipponMultiplicity_SectionThreeSupport
import Mathlib.RingTheory.Ideal.MinimalPrime.Localization
import Mathlib.RingTheory.KrullDimension.NonZeroDivisors
import Theorems.Thm_Module_depth_le_ringKrullDim_quotient_of_mem_associatedPrimes

-- Existing colon/localization and association helpers.
noncomputable section
namespace PhilipponMultiplicity.ComponentLength
variable {R : Type*} [CommRing R]
theorem localization_map_colon (S : Submonoid R) (A : Type*) [CommRing A]
    [Algebra R A] [IsLocalization S A] (I : Ideal R) (P : R) :
    (I.colon {P}).map (algebraMap R A) =
      (I.map (algebraMap R A)).colon {algebraMap R A P} := by
  ext z
  obtain ⟨x, s, rfl⟩ := IsLocalization.exists_mk'_eq S z
  rw [IsLocalization.mk'_mem_map_algebraMap_iff, Submodule.mem_colon_singleton,
    smul_eq_mul, ← IsLocalization.mk'_one (M := S) (S := A) P,
    ← IsLocalization.mk'_mul, mul_one, IsLocalization.mk'_mem_map_algebraMap_iff]
  simp only [Submodule.mem_colon_singleton, smul_eq_mul, mul_assoc]


end PhilipponMultiplicity.ComponentLength
end

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace PhilipponMultiplicity.ComponentSelection
variable {R : Type*} [CommRing R]

theorem associatedPrimes_quotient_eq (I : Ideal R) :
    associatedPrimes R (R ⧸ I) = I.associatedPrimes := by
  have hc (f : R) : (⊥ : Submodule R (R ⧸ I)).colon {Ideal.Quotient.mk I f} = I.colon {f} := by
    ext x
    simp only [Submodule.mem_colon_singleton, Submodule.mem_bot, Algebra.smul_def,
      Ideal.Quotient.algebraMap_eq, ← map_mul, Ideal.Quotient.eq_zero_iff_mem, smul_eq_mul]
    rfl
  ext q
  constructor
  · rintro ⟨hp, x, heq⟩
    obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective x
    exact ⟨hp, f, heq.trans (congrArg Ideal.radical (hc f))⟩
  · rintro ⟨hp, f, heq⟩
    exact ⟨hp, Ideal.Quotient.mk I f, heq.trans (congrArg Ideal.radical (hc f).symm)⟩

end PhilipponMultiplicity.ComponentSelection

end


set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace PhilipponMultiplicity.CohenMacaulaySupport
open IsLocalRing RingTheory
open PhilipponMultiplicity.ComponentSelection PhilipponMultiplicity.ComponentLength

/-- Strict containment of primes drops the quotient dimension by at least one.
The argument is also used in the accepted public depth proof. -/
theorem quotient_dimension_drop {R : Type*} [CommRing R]
    {p q : Ideal R} [p.IsPrime] (hpq : p < q) :
    ringKrullDim (R ⧸ q) + 1 ≤ ringKrullDim (R ⧸ p) := by
  obtain ⟨x, hxq, hxp⟩ := SetLike.exists_of_lt hpq
  refine ringKrullDim_succ_le_of_surjective (Ideal.Quotient.factor hpq.le)
    (Ideal.Quotient.factor_surjective hpq.le) (r := Ideal.Quotient.mk p x) ?_ ?_
  · exact mem_nonZeroDivisors_of_ne_zero
      fun h => hxp (Ideal.Quotient.eq_zero_iff_mem.mp h)
  · rw [Ideal.Quotient.factor_mk, Ideal.Quotient.eq_zero_iff_mem]
    exact hxq

/-- A full-length regular sequence forces every associated prime to be minimal. -/
theorem associated_isMinimal_of_regularSequence {R : Type*} [CommRing R]
    [IsLocalRing R] [IsNoetherianRing R]
    (rs : List R) (hrs : ∀ r ∈ rs, ¬ IsUnit r)
    (hreg : Sequence.IsRegular R rs)
    (hdim : (rs.length : WithBot ℕ∞) = ringKrullDim R)
    (p : Ideal R) (hp : p ∈ associatedPrimes R R) : p ∈ minimalPrimes R := by
  have hdepth : (rs.length : ℕ∞) ≤ Module.depth R R :=
    le_sSup ⟨rs, hreg.1, fun r hr => (mem_maximalIdeal _).mpr (hrs r hr), rfl⟩
  have heq : ringKrullDim (R ⧸ p) = ringKrullDim R := by
    refine le_antisymm (ringKrullDim_quotient_le p) ?_
    rw [← hdim]
    exact (WithBot.coe_le_coe.mpr hdepth).trans
      (Module.depth_le_ringKrullDim_quotient_of_mem_associatedPrimes R hp)
  rw [minimalPrimes_eq_minimals]
  refine ⟨hp.isPrime, ?_⟩
  intro q hq hqp
  by_contra hpq
  letI : q.IsPrime := hq
  have hdrop := quotient_dimension_drop (lt_of_le_not_ge hqp hpq)
  rw [heq, ← hdim] at hdrop
  have hupper := ringKrullDim_quotient_le q
  rw [← hdim] at hupper
  exact (lt_irrefl (rs.length : WithBot ℕ∞))
    (ENat.WithBot.add_one_le_iff.mp (hdrop.trans hupper))

variable {R : Type*} [CommRing R]

/-- Associated primes of a quotient remain associated when the quotient acts on itself. -/
theorem associated_quotient_self [IsNoetherianRing R] (I q : Ideal R)
    (hq : q ∈ associatedPrimes R (R ⧸ I)) :
    q.map (Ideal.Quotient.mk I) ∈ associatedPrimes (R ⧸ I) (R ⧸ I) := by
  have hass : I.IsAssociatedPrime q := by rwa [associatedPrimes_quotient_eq] at hq
  obtain ⟨hprime, r, heq⟩ := Submodule.isAssociatedPrime_iff.mp hass
  letI : q.IsPrime := hprime
  have hIq : I ≤ q := by
    rw [heq]
    intro x hx
    exact Submodule.mem_colon_singleton.mpr (I.mul_mem_right r hx)
  apply isAssociatedPrime_iff.mpr
  refine ⟨Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective
    (by simpa using hIq), Ideal.Quotient.mk I r, ?_⟩
  apply Ideal.comap_injective_of_surjective (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective
  rw [Ideal.comap_map_of_surjective _ Ideal.Quotient.mk_surjective,
    ← RingHom.ker_eq_comap_bot, Ideal.mk_ker, sup_eq_left.mpr hIq, heq]
  ext x
  simp only [Ideal.mem_comap, Submodule.mem_colon_singleton, Submodule.mem_bot,
    smul_eq_mul, ← map_mul, Ideal.Quotient.eq_zero_iff_mem]

end PhilipponMultiplicity.CohenMacaulaySupport

namespace PhilipponMultiplicity.Hilbert
open CohenMacaulaySupport ComponentSelection ComponentLength

theorem cohenMacaulayAt_associated_isMinimal
    {K : Type*} [Field K] (M : MultiProjectiveSpace K)
    (I : Ideal M.CoordinateRing) (m : MaximalSpectrum M.CoordinateRing)
    (hCM : Hilbert.IsCohenMacaulayAt K M.factorCount M.ambientDimension I m)
    (q : Ideal M.CoordinateRing)
    (hq : q ∈ associatedPrimes M.CoordinateRing (M.CoordinateRing ⧸ I))
    (hqm : q ≤ m.asIdeal) : q ∈ I.minimalPrimes := by
  let R := M.CoordinateRing
  let A := Localization.AtPrime m.asIdeal
  let f : R →+* A := algebraMap R A
  let J : Ideal A := I.map f
  let Q : Ideal A := q.map f
  let B := A ⧸ J
  letI : q.IsPrime := hq.isPrime
  have hdis : Disjoint (m.asIdeal.primeCompl : Set R) q := by
    exact Set.disjoint_left.mpr (fun x hxs hxq => hxs (hqm hxq))
  have hQprime : Q.IsPrime := IsLocalization.isPrime_of_isPrime_disjoint
    m.asIdeal.primeCompl A q hq.isPrime hdis
  letI : Q.IsPrime := hQprime
  have hQcomap : Q.comap f = q := IsLocalization.under_map_of_isPrime_disjoint
    m.asIdeal.primeCompl A hq.isPrime hdis
  have hass : I.IsAssociatedPrime q := by rwa [associatedPrimes_quotient_eq] at hq
  obtain ⟨_, r, heq⟩ := Submodule.isAssociatedPrime_iff.mp hass
  have hQA : Q ∈ associatedPrimes A B := by
    rw [associatedPrimes_quotient_eq]
    apply Submodule.isAssociatedPrime_iff.mpr
    refine ⟨hQprime, f r, ?_⟩
    exact (congrArg (Ideal.map f) heq).trans
      (localization_map_colon m.asIdeal.primeCompl A I r)
  haveI : Nontrivial B := not_subsingleton_iff_nontrivial.mp (by
    intro h
    letI : Subsingleton B := h
    exact not_isAssociatedPrime_of_subsingleton hQA)
  have hQB := associated_quotient_self J Q hQA
  letI : IsLocalRing B := IsLocalRing.of_surjective' (Ideal.Quotient.mk J)
    Ideal.Quotient.mk_surjective
  change Subsingleton B ∨ ∃ rs : List B,
    (∀ r ∈ rs, ¬ IsUnit r) ∧ RingTheory.Sequence.IsRegular B rs ∧
    (rs.length : WithBot ℕ∞) = ringKrullDim B at hCM
  rcases hCM with hzero | ⟨rs, hrs, hreg, hdim⟩
  · exact (not_subsingleton B hzero).elim
  have hmin := associated_isMinimal_of_regularSequence rs hrs hreg hdim _ hQB
  have hJQ : J ≤ Q := by
    apply Ideal.map_mono
    rw [heq]
    intro x hx
    exact Submodule.mem_colon_singleton.mpr (I.mul_mem_right r hx)
  have hminA : Q ∈ J.minimalPrimes := by
    have h := Ideal.minimalPrimes_comap_of_surjective Ideal.Quotient.mk_surjective hmin
    simpa only [minimalPrimes, ← RingHom.ker_eq_comap_bot, Ideal.mk_ker,
      Ideal.comap_map_of_surjective _ Ideal.Quotient.mk_surjective,
      sup_eq_left.mpr hJQ] using h
  rw [IsLocalization.minimalPrimes_map m.asIdeal.primeCompl A I] at hminA
  change Q.comap f ∈ I.minimalPrimes at hminA
  rwa [hQcomap] at hminA

end PhilipponMultiplicity.Hilbert
end

set_option autoImplicit false
open scoped BigOperators
open MvPolynomial PhilipponMultiplicity PhilipponMultiplicity.SectionThree
open PhilipponMultiplicity.SectionThreeSupport PhilipponMultiplicity.Hilbert
theorem solution
    {K : Type*} [Field K] (M : MultiProjectiveSpace K)
    (I : Ideal M.CoordinateRing) (m : MaximalSpectrum M.CoordinateRing)
    (hCM : Hilbert.IsCohenMacaulayAt K M.factorCount M.ambientDimension I m)
    (q : Ideal M.CoordinateRing)
    (hq : q ∈ associatedPrimes M.CoordinateRing (M.CoordinateRing ⧸ I))
    (hqm : q ≤ m.asIdeal) : q ∈ I.minimalPrimes := by
  exact PhilipponMultiplicity.Hilbert.cohenMacaulayAt_associated_isMinimal M I m hCM q hq hqm
