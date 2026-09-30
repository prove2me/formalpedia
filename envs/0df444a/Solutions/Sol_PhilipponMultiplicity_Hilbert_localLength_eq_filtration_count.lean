-- Prove2me | solution 1 for PhilipponMultiplicity.Hilbert.localLength_eq_filtration_count
-- status  : ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-09-26T01:02:25.419248+00:00
-- url     : https://prove2.me/submissions/1d1dcb27-8808-4da0-a89f-9b5ffe580874

import Definitions.Def_PhilipponMultiplicity_SectionThree
set_option autoImplicit false
open scoped BigOperators
open MvPolynomial PhilipponMultiplicity PhilipponMultiplicity.SectionThree
open PhilipponMultiplicity.Hilbert

-- Reused from Solutions/PhilipponColonLength.lean

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators
noncomputable section

namespace PhilipponMultiplicity.ComponentLength
variable {R : Type*} [CommRing R]

/-- Length additivity for the actual cyclic colon exact sequence, allowing
infinite lengths and zero divisors. -/
theorem quotient_length_colon_add (I : Ideal R) (P : R) :
    Module.length R (R ⧸ I) = Module.length R (R ⧸ I.colon {P}) +
      Module.length R (R ⧸ (I ⊔ Ideal.span {P})) := by
  let C := I.colon {P}
  let J := I ⊔ Ideal.span {P}
  let f : (R ⧸ C) →ₗ[R] (R ⧸ I) := C.liftQ
    (I.mkQ.comp (LinearMap.mulLeft R P)) (by
      intro Q hQ
      change Ideal.Quotient.mk I (P * Q) = 0
      apply Ideal.Quotient.eq_zero_iff_mem.mpr
      change Q ∈ I.colon {P} at hQ
      change P * Q ∈ I
      simpa only [Submodule.mem_colon_singleton, smul_eq_mul, mul_comm] using hQ)
  let g : (R ⧸ I) →ₗ[R] (R ⧸ J) := Submodule.factor (show I ≤ J from le_sup_left)
  have hf : Function.Injective f := by
    rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
    intro x hx
    obtain ⟨Q, rfl⟩ := Ideal.Quotient.mk_surjective x
    apply Ideal.Quotient.eq_zero_iff_mem.mpr
    rw [Submodule.mem_colon_singleton, smul_eq_mul, mul_comm]
    exact Ideal.Quotient.eq_zero_iff_mem.mp (LinearMap.mem_ker.mp hx)
  have hg : Function.Surjective g := by
    intro x
    obtain ⟨Q, rfl⟩ := Ideal.Quotient.mk_surjective x
    exact ⟨Ideal.Quotient.mk I Q, rfl⟩
  have hexact : Function.Exact f g := by
    intro x
    obtain ⟨Q, rfl⟩ := Ideal.Quotient.mk_surjective x
    change Ideal.Quotient.mk J Q = 0 ↔ _
    rw [Ideal.Quotient.eq_zero_iff_mem]
    constructor
    · intro hQ
      obtain ⟨a, b, hb, heq⟩ := Ideal.mem_span_singleton_sup.mp
        (show Q ∈ Ideal.span {P} ⊔ I by simpa only [sup_comm] using hQ)
      refine ⟨Ideal.Quotient.mk C a, ?_⟩
      change Ideal.Quotient.mk I (P * a) = Ideal.Quotient.mk I Q
      rw [← heq, map_add, Ideal.Quotient.eq_zero_iff_mem.mpr hb, add_zero, mul_comm]
    · rintro ⟨y, hy⟩
      obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective y
      have hqa : Q - P * a ∈ I := by
        apply Ideal.Quotient.eq.mp
        exact hy.symm
      have hpa : P * a ∈ J := J.mul_mem_right a
        ((le_sup_right : Ideal.span {P} ≤ J) (Ideal.subset_span (Set.mem_singleton P)))
      simpa only [sub_add_cancel] using J.add_mem ((le_sup_left : I ≤ J) hqa) hpa
  exact Module.length_eq_add_of_exact f g hf hg hexact

/-- Localization commutes with colon by one element. -/
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

-- Reused from Solutions/PhilipponFiltrationLength.lean

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators
noncomputable section

namespace PhilipponMultiplicity.Hilbert
variable {K : Type*} [Field K] (M : MultiProjectiveSpace K)

theorem localLength_colon_add (I : Ideal M.CoordinateRing) (P : M.CoordinateRing)
    (q : PrimeSpectrum M.CoordinateRing) :
    localLength K M.factorCount M.ambientDimension I q =
      localLength K M.factorCount M.ambientDimension (I.colon {P}) q +
      localLength K M.factorCount M.ambientDimension (I ⊔ Ideal.span {P}) q := by
  unfold localLength
  rw [ComponentLength.quotient_length_colon_add _ (algebraMap _ (Localization.AtPrime q.asIdeal) P),
    ← ComponentLength.localization_map_colon q.asIdeal.primeCompl,
    Ideal.map_sup, Ideal.map_span, Set.image_singleton]

theorem localLength_filtration_sum (n : ℕ)
    (J : Fin (n + 1) → Ideal M.CoordinateRing) (P : Fin n → M.CoordinateRing)
    (hstep : ∀ j, J j.succ = J j.castSucc ⊔ Ideal.span {P j})
    (hlast : J (Fin.last n) = ⊤) (q : PrimeSpectrum M.CoordinateRing) :
    localLength K M.factorCount M.ambientDimension (J 0) q =
      ∑ j, localLength K M.factorCount M.ambientDimension ((J j.castSucc).colon {P j}) q := by
  induction n with
  | zero =>
    have heq : J 0 = ⊤ := hlast
    rw [heq]
    rw [Fin.sum_univ_zero, localLength, Ideal.map_top]
    exact Module.length_eq_zero
  | succ n ih =>
    rw [Fin.sum_univ_succ]
    have htail := ih (fun j => J j.succ) (fun j => P j.succ)
      (fun j => by simpa using hstep j.succ) hlast
    have hfirst := localLength_colon_add M (J 0) (P 0) q
    have hzero : J (Fin.succ 0) = J 0 ⊔ Ideal.span {P 0} := hstep 0
    rw [← hzero, htail] at hfirst
    simpa only [Fin.castSucc_zero, Fin.castSucc_succ] using hfirst

theorem localLength_prime_at_minimal (I Q : Ideal M.CoordinateRing)
    (hQ : Q.IsPrime) (hIQ : I ≤ Q) (q : PrimeSpectrum M.CoordinateRing)
    (hq : q.asIdeal ∈ I.minimalPrimes) :
    localLength K M.factorCount M.ambientDimension Q q = if Q = q.asIdeal then 1 else 0 := by
  classical
  by_cases heq : Q = q.asIdeal
  · rw [if_pos heq, heq, localLength, IsLocalization.AtPrime.map_eq_maximalIdeal]
    letI : IsSimpleModule (Localization.AtPrime q.asIdeal)
        ((Localization.AtPrime q.asIdeal) ⧸ IsLocalRing.maximalIdeal (Localization.AtPrime q.asIdeal)) :=
      isSimpleModule_iff_isCoatom.mpr (Ideal.isMaximal_def.mp inferInstance)
    exact Module.length_eq_one _ _
  · rw [if_neg heq, localLength]
    have hnot : ¬ Q ≤ q.asIdeal := by
      intro hle
      exact heq (le_antisymm hle (hq.2 ⟨hQ, hIQ⟩ hle))
    rw [IsLocalization.AtPrime.map_eq_top_of_not_le _ hnot]
    exact Module.length_eq_zero

/-- At every actual minimal prime, the number of matching prime factors in
any finite cyclic prime filtration is exactly the actual generic length. -/
theorem localLength_eq_filtration_count (I : Ideal M.CoordinateRing) (n : ℕ)
    (J : Fin (n + 1) → Ideal M.CoordinateRing) (P : Fin n → M.CoordinateRing)
    (hfirst : J 0 = I) (hlast : J (Fin.last n) = ⊤)
    (hstep : ∀ j, J j.succ = J j.castSucc ⊔ Ideal.span {P j})
    (hprime : ∀ j, ((J j.castSucc).colon {P j}).IsPrime)
    (q : PrimeSpectrum M.CoordinateRing) (hq : q.asIdeal ∈ I.minimalPrimes) :
    (localLength K M.factorCount M.ambientDimension I q).toNat =
      ∑ j, if (J j.castSucc).colon {P j} = q.asIdeal then 1 else 0 := by
  classical
  have hmono : Monotone J := Fin.monotone_iff_le_succ.mpr (fun j => by
    rw [hstep j]; exact le_sup_left)
  have hIQ (j : Fin n) : I ≤ (J j.castSucc).colon {P j} := by
    rw [← hfirst]
    exact (hmono (Fin.zero_le _)).trans Ideal.le_colon
  have hsum := localLength_filtration_sum M n J P hstep hlast q
  rw [hfirst] at hsum
  simp_rw [localLength_prime_at_minimal M I _ (hprime _) (hIQ _) q hq] at hsum
  have hcast : localLength K M.factorCount M.ambientDimension I q =
      ((∑ j, if (J j.castSucc).colon {P j} = q.asIdeal then 1 else 0 : ℕ) : ℕ∞) := by
    simpa using hsum
  rw [hcast, ENat.toNat_natCast]

end PhilipponMultiplicity.Hilbert

end

theorem solution
    {K : Type*} [Field K] (M : MultiProjectiveSpace K) (I : Ideal M.CoordinateRing) (n : ℕ)
    (J : Fin (n + 1) → Ideal M.CoordinateRing) (P : Fin n → M.CoordinateRing)
    (hfirst : J 0 = I) (hlast : J (Fin.last n) = ⊤)
    (hstep : ∀ j, J j.succ = J j.castSucc ⊔ Ideal.span {P j})
    (hprime : ∀ j, ((J j.castSucc).colon {P j}).IsPrime)
    (q : PrimeSpectrum M.CoordinateRing) (hq : q.asIdeal ∈ I.minimalPrimes) :
    (localLength K M.factorCount M.ambientDimension I q).toNat =
      ∑ j, if (J j.castSucc).colon {P j} = q.asIdeal then 1 else 0 := by
  exact PhilipponMultiplicity.Hilbert.localLength_eq_filtration_count M I n J P hfirst hlast hstep hprime q hq
