-- Prove2me | solution 1 for WeierstrassEllipticZeta.curvilinear_chart_length_realization
-- status  : ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-09-21T09:40:04.322196+00:00
-- url     : https://prove2.me/submissions/4313fba1-0a68-4240-81d9-34143d866aa5

import Definitions.Def_WeierstrassEllipticZeta_CurvilinearChartJets
import Mathlib.Tactic
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.RingTheory.Localization.Ideal
import Mathlib.RingTheory.Localization.Submodule
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Theorems.Thm_TranscendenceTheory_punctual_ideal_finite_jet_characterization
import Theorems.Thm_TranscendenceTheory_finite_zero_locus_quotient_geometry
import Theorems.Thm_TranscendenceTheory_finite_algebra_local_multiplicity_dimension

open WeierstrassEllipticZeta MvPolynomial TranscendenceTheory


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

theorem curvilinear_cubic_mem (L : PeriodPair) (a b : ℂ) (e : ℕ)
    (hb : b ^ 2 = -L.g₃) :
    extensionChartCubic L.g₂ L.g₃ 0 ∈ curvilinearChartIdeal a b e := by
  change Ideal.Quotient.mk _
    (MvPolynomial.aeval ![Polynomial.X + Polynomial.C a, 0, Polynomial.C b, 0]
      (extensionChartCubic L.g₂ L.g₃ 0)) = 0
  have hp : MvPolynomial.aeval ![Polynomial.X + Polynomial.C a, 0, Polynomial.C b, 0]
      (extensionChartCubic L.g₂ L.g₃ 0) = Polynomial.C (b ^ 2 + L.g₃) := by
    simp [extensionChartCubic]
  rw [hp, hb, neg_add_cancel, map_zero, map_zero]

end WeierstrassEllipticZeta


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

theorem finite_jet_local_length_eq_dimension {L : PeriodPair} {ι : Type}
    (J : FiniteJetChartIdealData L ι) (i : ι) :
    J.localLength i = Module.finrank ℂ (MvPolynomial (Fin 4) ℂ ⧸ J.ideal i) := by
  apply punctual_local_length_eq_dimension
  exact (punctual_ideal_finite_jet_characterization ℂ (Fin 4) (J.ideal i) (J.point i)).1.mpr
    ⟨J.power_le i, J.le_point i⟩

end WeierstrassEllipticZeta

open WeierstrassEllipticZeta MvPolynomial TranscendenceTheory

theorem solution
    (L : PeriodPair) (ι : Type) [Fintype ι] :
    (∀ (J : FiniteJetChartIdealData L ι) (i : ι),
      0 < J.localLength i ∧
      J.localLength i = Module.finrank ℂ (MvPolynomial (Fin 4) ℂ ⧸ J.ideal i)) ∧
    (∀ e : ι → ℕ, (∀ i, 0 < e i) →
      ∃ a : ι → ℂ, Function.Injective a ∧
      ∃ b : ℂ, b ^ 2 = -L.g₃ ∧
      ∃ J : FiniteJetChartIdealData L ι, ∀ i,
        J.point i = ![a i, 0, b, 0] ∧
        J.ideal i = curvilinearChartIdeal (a i) b (e i) ∧
        J.localLength i = e i ∧
        Module.finrank ℂ (MvPolynomial (Fin 4) ℂ ⧸ J.ideal i) = e i) := by
  classical
  refine ⟨?_, ?_⟩
  · intro J i
    have he := finite_jet_local_length_eq_dimension J i
    refine ⟨?_, he⟩
    rw [he]
    exact ((punctual_ideal_finite_jet_characterization ℂ (Fin 4) (J.ideal i) (J.point i)).2
      ((punctual_ideal_finite_jet_characterization ℂ (Fin 4) (J.ideal i) (J.point i)).1.mpr
        ⟨J.power_le i, J.le_point i⟩)).1
  · intro e he
    let a : ι → ℂ := fun i => ((Fintype.equivFin ι i).val : ℂ)
    have ha : Function.Injective a := by
      intro i j hij
      apply (Fintype.equivFin ι).injective
      apply Fin.ext
      exact Nat.cast_injective hij
    obtain ⟨b, hb⟩ := IsAlgClosed.exists_pow_nat_eq (-L.g₃) (by norm_num : 0 < (2 : ℕ))
    let J : FiniteJetChartIdealData L ι :=
      { point := fun i => ![a i, 0, b, 0]
        point_injective := by
          intro i j hij
          exact ha (congrFun hij 0)
        ideal := fun i => curvilinearChartIdeal (a i) b (e i)
        cubic_mem := fun i => curvilinear_cubic_mem L (a i) b (e i) hb
        power_le := fun i => ((punctual_ideal_finite_jet_characterization ℂ (Fin 4)
          (curvilinearChartIdeal (a i) b (e i)) ![a i, 0, b, 0]).1.mp
            (curvilinear_zero_locus (a i) b (e i) (he i))).1
        le_point := fun i => ((punctual_ideal_finite_jet_characterization ℂ (Fin 4)
          (curvilinearChartIdeal (a i) b (e i)) ![a i, 0, b, 0]).1.mp
            (curvilinear_zero_locus (a i) b (e i) (he i))).2 }
    refine ⟨a, ha, b, hb, J, ?_⟩
    intro i
    refine ⟨rfl, rfl, ?_, curvilinear_quotient_dimension (a i) b (e i)⟩
    rw [finite_jet_local_length_eq_dimension]
    exact curvilinear_quotient_dimension (a i) b (e i)
