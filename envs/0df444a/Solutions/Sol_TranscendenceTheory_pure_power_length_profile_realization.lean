-- Prove2me | solution 1 for TranscendenceTheory.pure_power_length_profile_realization
-- status  : ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-09-22T05:57:19.417485+00:00
-- url     : https://prove2.me/submissions/99556bb7-2897-489c-9dd1-6b68da284854

import Definitions.Def_WeierstrassEllipticZeta_CurvilinearChartJets
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Polynomial.Monic
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Data.Finsupp.MonomialOrder.DegLex
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.RingTheory.Artinian.Module
import Mathlib.RingTheory.Finiteness.Basic
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.IntegralClosure.IsIntegral.Basic
import Mathlib.RingTheory.Length
import Mathlib.RingTheory.LocalRing.Length
import Mathlib.RingTheory.Localization.Ideal
import Mathlib.RingTheory.Localization.Submodule
import Mathlib.RingTheory.MvPolynomial.Basic
import Mathlib.RingTheory.MvPolynomial.Groebner
import Mathlib.RingTheory.Nullstellensatz
import Mathlib.RingTheory.Spectrum.Prime.Noetherian
import Mathlib.Tactic
import Theorems.Thm_TranscendenceTheory_pure_power_standard_monomial_basis
import Theorems.Thm_TranscendenceTheory_finite_algebra_local_multiplicity_dimension
import Theorems.Thm_TranscendenceTheory_finite_zero_locus_quotient_geometry

noncomputable section
open MvPolynomial
open scoped MonomialOrder

noncomputable section
namespace WeierstrassEllipticZeta
open MvPolynomial TranscendenceTheory

theorem curvilinear_restriction_surjective (a b : ℂ) (e : ℕ) :
    Function.Surjective (curvilinearChartRestriction a b e) := by
  let f : Polynomial ℂ →ₐ[ℂ] MvPolynomial (Fin 4) ℂ := Polynomial.aeval (X 0 - C a)
  have he : (curvilinearChartRestriction a b e).comp f =
      Ideal.Quotient.mkₐ ℂ (Ideal.span {(Polynomial.X : Polynomial ℂ) ^ e}) := by
    ext
    simp [f, curvilinearChartRestriction]
  intro q
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective q
  exact ⟨f p, DFunLike.congr_fun he p⟩

theorem curvilinear_quotient_dimension (a b : ℂ) (e : ℕ) :
    Module.finrank ℂ (MvPolynomial (Fin 4) ℂ ⧸ curvilinearChartIdeal a b e) = e := by
  let f := Ideal.quotientKerAlgEquivOfSurjective (curvilinear_restriction_surjective a b e)
  change Module.finrank ℂ (MvPolynomial (Fin 4) ℂ ⧸ RingHom.ker
    (curvilinearChartRestriction a b e)) = e
  rw [f.toLinearEquiv.finrank_eq, finrank_quotient_span_eq_natDegree]
  simp

theorem curvilinear_zero_locus (a b : ℂ) (e : ℕ) (he : 0 < e) :
    zeroLocus ℂ (curvilinearChartIdeal a b e) = {![a, 0, b, 0]} := by
  have hp0 : (X 0 - C a) ^ e ∈ curvilinearChartIdeal a b e := by
    change (curvilinearChartRestriction a b e) ((X 0 - C a) ^ e) = 0
    simpa [curvilinearChartRestriction] using
      (Ideal.Quotient.eq_zero_iff_mem.mpr
        (Ideal.subset_span (Set.mem_singleton ((Polynomial.X : Polynomial ℂ) ^ e))) :
          Ideal.Quotient.mk (Ideal.span {(Polynomial.X : Polynomial ℂ) ^ e})
            ((Polynomial.X : Polynomial ℂ) ^ e) = 0)
  have hp1 : X 1 ∈ curvilinearChartIdeal a b e := by
    change (curvilinearChartRestriction a b e) (X 1) = 0
    simp [curvilinearChartRestriction]
  have hp2 : X 2 - C b ∈ curvilinearChartIdeal a b e := by
    change (curvilinearChartRestriction a b e) (X 2 - C b) = 0
    simp [curvilinearChartRestriction]
  have hp3 : X 3 ∈ curvilinearChartIdeal a b e := by
    change (curvilinearChartRestriction a b e) (X 3) = 0
    simp [curvilinearChartRestriction]
  have hcomp : (Polynomial.aeval (0 : ℂ)).comp
      (MvPolynomial.aeval ![Polynomial.X + Polynomial.C a, 0, Polynomial.C b, 0]) =
        MvPolynomial.aeval ![a, 0, b, 0] := by
    ext i
    fin_cases i <;> simp
  ext x
  constructor
  · intro hx
    have h0 : (x 0 - a) ^ e = 0 := by simpa using hx _ hp0
    have h1 : x 1 = 0 := by simpa using hx _ hp1
    have h2 : x 2 - b = 0 := by simpa using hx _ hp2
    have h3 : x 3 = 0 := by simpa using hx _ hp3
    rw [Set.mem_singleton_iff]
    ext i
    fin_cases i
    · exact sub_eq_zero.mp (eq_zero_of_pow_eq_zero h0)
    · exact h1
    · exact sub_eq_zero.mp h2
    · exact h3
  · rintro rfl p hp
    change Ideal.Quotient.mk (Ideal.span {(Polynomial.X : Polynomial ℂ) ^ e})
      (MvPolynomial.aeval ![Polynomial.X + Polynomial.C a, 0, Polynomial.C b, 0] p) = 0 at hp
    obtain ⟨q, hq⟩ := Ideal.mem_span_singleton.mp (Ideal.Quotient.eq_zero_iff_mem.mp hp)
    have hz := DFunLike.congr_fun hcomp p
    rw [AlgHom.comp_apply] at hz
    rw [← hz, hq]
    simp [he.ne']


end WeierstrassEllipticZeta


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


noncomputable section
namespace WeierstrassEllipticZeta
open MvPolynomial TranscendenceTheory

theorem punctual_local_length_eq_dimension
    (I : Ideal (MvPolynomial (Fin 4) ℂ)) (x : Fin 4 → ℂ)
    (hzero : zeroLocus ℂ I = {x}) :
    (Module.length (Localization.AtPrime (pointToPoint (k := ℂ) x).asIdeal)
      ((Localization.AtPrime (pointToPoint (k := ℂ) x).asIdeal) ⧸ I.map
        (algebraMap (MvPolynomial (Fin 4) ℂ)
          (Localization.AtPrime (pointToPoint (k := ℂ) x).asIdeal)))).toNat =
      Module.finrank ℂ (MvPolynomial (Fin 4) ℂ ⧸ I) := by
  classical
  let R := MvPolynomial (Fin 4) ℂ
  let A := R ⧸ I
  let : Module.Finite ℂ A := (finite_zero_locus_quotient_geometry ℂ (Fin 4) I).1.mpr
    (hzero ▸ Set.finite_singleton x)
  let p := pointToPoint (k := ℂ) x
  have hIp : I ≤ p.asIdeal := by
    intro f hf
    exact (mem_vanishingIdeal_singleton_iff x f).mpr
      ((show x ∈ zeroLocus ℂ I by rw [hzero]; exact Set.mem_singleton x) f hf)
  let q : PrimeSpectrum A :=
    ⟨p.asIdeal.map (Ideal.Quotient.mk I), Ideal.isPrime_map_quotientMk_of_isPrime hIp⟩
  have hq (r : PrimeSpectrum A) : r = q := by
    let s := PrimeSpectrum.comap (Ideal.Quotient.mk I) r
    have hIs : I ≤ s.asIdeal := by
      intro f hf
      change Ideal.Quotient.mk I f ∈ r.asIdeal
      rw [Ideal.Quotient.eq_zero_iff_mem.mpr hf]
      exact r.asIdeal.zero_mem
    obtain ⟨y, hy, hs⟩ := (finite_zero_locus_quotient_geometry ℂ (Fin 4) I).2.2
      inferInstance s hIs
    have hyx : y = x := by simpa only [hzero, Set.mem_singleton_iff] using hy
    apply PrimeSpectrum.comap_injective_of_surjective (Ideal.Quotient.mk I)
      Ideal.Quotient.mk_surjective
    apply PrimeSpectrum.ext
    change s.asIdeal = (p.asIdeal.map (Ideal.Quotient.mk I)).comap (Ideal.Quotient.mk I)
    rw [Ideal.comap_map_mk hIp]
    simpa only [hyx, p] using congrArg PrimeSpectrum.asIdeal hs.symm
  have he := ((finite_algebra_local_multiplicity_dimension ℂ A).2
    Unit (fun _ => q) (fun _ _ _ => Subsingleton.elim _ _)).2
      (fun r => ⟨Unit.unit, (hq r).symm⟩)
  have hloc := quotient_localization_length_eq R I p.asIdeal hIp
  change (Module.length (Localization.AtPrime p.asIdeal)
    ((Localization.AtPrime p.asIdeal) ⧸ I.map (algebraMap R (Localization.AtPrime p.asIdeal)))).toNat = _
  rw [hloc]
  simpa only [Fintype.sum_unique] using he


end WeierstrassEllipticZeta


noncomputable section

namespace TranscendenceTheory

open MvPolynomial WeierstrassEllipticZeta
open scoped MonomialOrder

theorem pure_power_profile_leading_terms
    (ι : Type) [Fintype ι] (a : ι → ℂ) (e : ι → ℕ)
    (o : MonomialOrder (Fin 4)) :
    let b : Fin 4 → MvPolynomial (Fin 4) ℂ :=
      ![∏ i, (X 0 - C (a i)) ^ e i, X 1, X 2, X 3]
    let d : Fin 4 → ℕ := ![∑ i, e i, 1, 1, 1]
    (∀ i, IsUnit (o.leadingCoeff (b i))) ∧
      (∀ i, o.degree (b i) = Finsupp.single i (d i)) := by
  classical
  dsimp only
  have hn (i : ι) : (X 0 - C (a i) : MvPolynomial (Fin 4) ℂ) ≠ 0 := by
    intro h
    have hd := o.degree_X_sub_C (0 : Fin 4) (a i)
    rw [h, o.degree_zero] at hd
    have hbad := congrArg (fun c : Fin 4 →₀ ℕ => c 0) hd
    simp at hbad
  constructor
  · intro i
    apply o.isUnit_leadingCoeff.mpr
    fin_cases i
    · exact Finset.prod_ne_zero_iff.mpr (fun j _ => pow_ne_zero _ (hn j))
    all_goals exact X_ne_zero _
  · intro i
    fin_cases i
    · change o.degree (∏ j, (X 0 - C (a j)) ^ e j) =
        Finsupp.single 0 (∑ j, e j)
      rw [o.degree_prod (fun j _ => pow_ne_zero _ (hn j))]
      simp_rw [o.degree_pow, o.degree_X_sub_C]
      simp only [nsmul_eq_mul, mul_one, Finsupp.smul_single]
      ext j
      by_cases hj : j = 0
      · subst j; simp
      · simp [Finsupp.single_apply, hj, Ne.symm hj]
    all_goals simpa using (o.degree_X (s := _))


end TranscendenceTheory

open TranscendenceTheory WeierstrassEllipticZeta MvPolynomial
theorem solution
    (ι : Type) [Fintype ι] (a : ι → ℂ) (ha : Function.Injective a)
    (e : ι → ℕ) (he : ∀ i, 0 < e i) (o : MonomialOrder (Fin 4)) :
    let b : Fin 4 → MvPolynomial (Fin 4) ℂ :=
      ![∏ i, (X 0 - C (a i)) ^ e i, X 1, X 2, X 3]
    let d : Fin 4 → ℕ := ![∑ i, e i, 1, 1, 1]
    let J : Ideal (MvPolynomial (Fin 4) ℂ) := Ideal.span (Set.range b)
    (∀ i, IsUnit (o.leadingCoeff (b i))) ∧
      (∀ i, o.degree (b i) = Finsupp.single i (d i)) ∧
      Module.Finite ℂ (MvPolynomial (Fin 4) ℂ ⧸ J) ∧
      Module.finrank ℂ (MvPolynomial (Fin 4) ℂ ⧸ J) = ∑ i, e i ∧
      ∃ p : ι → PrimeSpectrum (MvPolynomial (Fin 4) ℂ ⧸ J),
        Function.Injective p ∧ ∀ i,
          Module.length (Localization.AtPrime (p i).asIdeal)
            (Localization.AtPrime (p i).asIdeal) ≠ ⊤ ∧
          (Module.length (Localization.AtPrime (p i).asIdeal)
            (Localization.AtPrime (p i).asIdeal)).toNat = e i := by
  classical
  dsimp only
  let b : Fin 4 → MvPolynomial (Fin 4) ℂ :=
    ![∏ i, (X 0 - C (a i)) ^ e i, X 1, X 2, X 3]
  let d : Fin 4 → ℕ := ![∑ i, e i, 1, 1, 1]
  let J : Ideal (MvPolynomial (Fin 4) ℂ) := Ideal.span (Set.range b)
  obtain ⟨hu, hd⟩ := pure_power_profile_leading_terms ι a e o
  obtain ⟨hfinite, _, hdim, _⟩ := pure_power_standard_monomial_basis ℂ (Fin 4) o d b hu hd
  let := hfinite
  have hdimension : Module.finrank ℂ (MvPolynomial (Fin 4) ℂ ⧸ J) = ∑ i, e i := by
    simpa [d, Fin.prod_univ_succ] using hdim
  let x : ι → Fin 4 → ℂ := fun i => ![a i, 0, 0, 0]
  let P : ι → PrimeSpectrum (MvPolynomial (Fin 4) ℂ) :=
    fun i => pointToPoint (k := ℂ) (x i)
  let I : ι → Ideal (MvPolynomial (Fin 4) ℂ) :=
    fun i => curvilinearChartIdeal (a i) 0 (e i)
  have hJI (i : ι) : J ≤ I i := by
    apply Ideal.span_le.mpr
    rintro _ ⟨j, rfl⟩
    fin_cases j
    · change curvilinearChartRestriction (a i) 0 (e i)
        (∏ j, (X 0 - C (a j)) ^ e j) = 0
      rw [map_prod]
      apply Finset.prod_eq_zero (Finset.mem_univ i)
      change curvilinearChartRestriction (a i) 0 (e i) ((X 0 - C (a i)) ^ e i) = 0
      simpa [curvilinearChartRestriction] using
        (Ideal.Quotient.eq_zero_iff_mem.mpr
          (Ideal.subset_span (Set.mem_singleton ((Polynomial.X : Polynomial ℂ) ^ e i))) :
            Ideal.Quotient.mk (Ideal.span {(Polynomial.X : Polynomial ℂ) ^ e i})
              ((Polynomial.X : Polynomial ℂ) ^ e i) = 0)
    all_goals
      change curvilinearChartRestriction (a i) 0 (e i) _ = 0
      simp [b, curvilinearChartRestriction]
  have hIP (i : ι) : I i ≤ (P i).asIdeal := by
    intro f hf
    apply (mem_vanishingIdeal_singleton_iff (x i) f).mpr
    have hx : x i ∈ zeroLocus ℂ (I i) := by
      rw [curvilinear_zero_locus (a i) 0 (e i) (he i)]
      exact Set.mem_singleton _
    exact hx f hf
  have hJP (i : ι) : J ≤ (P i).asIdeal := (hJI i).trans (hIP i)
  let p : ι → PrimeSpectrum (MvPolynomial (Fin 4) ℂ ⧸ J) := fun i =>
    ⟨(P i).asIdeal.map (Ideal.Quotient.mk J),
      Ideal.isPrime_map_quotientMk_of_isPrime (hJP i)⟩
  have hp : Function.Injective p := by
    intro i j hij
    apply ha
    have hP : (P i).asIdeal = (P j).asIdeal := by
      have h := congrArg (fun q : PrimeSpectrum (MvPolynomial (Fin 4) ℂ ⧸ J) =>
        q.asIdeal.comap (Ideal.Quotient.mk J)) hij
      simpa only [p, Ideal.comap_map_mk (hJP i), Ideal.comap_map_mk (hJP j)] using h
    have hi : (X 0 - C (a i)) ∈ (P i).asIdeal := by
      change (X 0 - C (a i)) ∈ vanishingIdeal ℂ {x i}
      simp [x]
    rw [hP] at hi
    change (X 0 - C (a i)) ∈ vanishingIdeal ℂ {x j} at hi
    have h : a j - a i = 0 := by
      simpa [x] using (mem_vanishingIdeal_singleton_iff (x j) _).mp hi
    exact (sub_eq_zero.mp h).symm
  obtain ⟨hlocal, hsum⟩ := finite_algebra_local_multiplicity_dimension
    ℂ (MvPolynomial (Fin 4) ℂ ⧸ J)
  letI (i : ι) : (p i).asIdeal.IsPrime := (p i).isPrime
  have hlower (i : ι) : e i ≤
      (Module.length (Localization.AtPrime (p i).asIdeal)
        (Localization.AtPrime (p i).asIdeal)).toNat := by
    let Rp := Localization.AtPrime (P i).asIdeal
    have hmap : J.map (algebraMap _ Rp) ≤ (I i).map (algebraMap _ Rp) :=
      Ideal.map_mono (hJI i)
    have hle := Module.length_le_of_surjective
      (Ideal.Quotient.factorₐ Rp hmap).toLinearMap (Ideal.Quotient.factor_surjective hmap)
    have hquot := quotient_localization_length_eq (MvPolynomial (Fin 4) ℂ) J
      (P i).asIdeal (hJP i)
    rw [hquot] at hle
    have hn := ENat.toNat_le_toNat hle (hlocal (p i))
    have hsingle := punctual_local_length_eq_dimension (I i) (x i)
      (curvilinear_zero_locus (a i) 0 (e i) (he i))
    rw [hsingle, curvilinear_quotient_dimension] at hn
    exact hn
  have heq : ∀ i,
      (Module.length (Localization.AtPrime (p i).asIdeal)
        (Localization.AtPrime (p i).asIdeal)).toNat = e i := by
    have hs := (hsum ι p hp).1
    rw [hdimension] at hs
    have hs' := Finset.sum_le_sum (s := Finset.univ) (fun i _ => hlower i)
    have hall := (Finset.sum_eq_sum_iff_of_le (fun i _ => hlower i)).mp
      (le_antisymm hs' hs)
    intro i
    exact (hall i (Finset.mem_univ i)).symm
  exact ⟨hu, hd, hfinite, hdimension, p, hp, fun i => ⟨hlocal (p i), heq i⟩⟩
