-- Prove2me | solution 1 for PhilipponMultiplicity.normalized_principal_chart_domain_and_dimension
-- status  : ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-10-08T08:57:56.335237+00:00
-- url     : https://prove2.me/submissions/8e4a458a-ddd6-4891-9ad4-a66232b899bc

import Theorems.Thm_PhilipponMultiplicity_normalized_affine_chart_domain_and_dimension
import Definitions.Def_PhilipponMultiplicity_GeometricSupport
import Definitions.Def_PhilipponMultiplicity_MixedFlagParameters
import Definitions.Def_PhilipponMultiplicity_UniversalMixedSlices
import Mathlib


section

/- Reused verbatim proof bodies from PhilipponAffineAltitudeKernelAudit.lean,
   through height_eq_ringKrullDim_of_isMaximal. Only the outer namespace and
   unused P2M_Util import are changed. -/

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace PhilipponMultiplicity.AffineDimensionReuse

set_option autoImplicit false

universe u v

namespace P2mDimFormula

open Ideal Polynomial

private lemma exists_ltSeries_comap_eq_last {R S : Type*} [CommRing R] [CommRing S]
    [Algebra R S] [Algebra.IsIntegral R S] (hinj : Function.Injective (algebraMap R S))
    (l : LTSeries (PrimeSpectrum R)) :
    ∃ L : LTSeries (PrimeSpectrum S), L.length = l.length ∧
      PrimeSpectrum.comap (algebraMap R S) L.last = l.last := by
  haveI : FaithfulSMul R S := (faithfulSMul_iff_algebraMap_injective R S).mpr hinj
  induction l using RelSeries.inductionOn' with
  | singleton x =>
    obtain ⟨q, hq⟩ := Algebra.IsIntegral.comap_surjective R S x
    exact ⟨RelSeries.singleton _ q, rfl, hq⟩
  | snoc l x hx ih =>
    obtain ⟨L, hlen, hlast⟩ := ih
    have hle : L.last.asIdeal.comap (algebraMap R S) ≤ x.asIdeal := by
      have h1 : PrimeSpectrum.comap (algebraMap R S) L.last ≤ x := hlast ▸ le_of_lt hx
      exact (PrimeSpectrum.asIdeal_le_asIdeal _ _).mpr h1
    obtain ⟨Q, hQge, hQprime, hQcomap⟩ :=
      Ideal.exists_ideal_over_prime_of_isIntegral x.asIdeal L.last.asIdeal hle
    have hlx : l.last < x := hx
    have hQlt : L.last < (⟨Q, hQprime⟩ : PrimeSpectrum S) := by
      refine lt_of_le_of_ne ((PrimeSpectrum.asIdeal_le_asIdeal _ _).mp hQge) ?_
      intro h
      refine absurd ?_ (ne_of_lt hlx)
      calc l.last = PrimeSpectrum.comap (algebraMap R S) L.last := hlast.symm
        _ = PrimeSpectrum.comap (algebraMap R S) ⟨Q, hQprime⟩ := by rw [h]
        _ = x := PrimeSpectrum.ext hQcomap
    refine ⟨L.snoc ⟨Q, hQprime⟩ hQlt, by simp [hlen], ?_⟩
    simp only [RelSeries.last_snoc]
    exact PrimeSpectrum.ext hQcomap

theorem ringKrullDim_eq_of_isIntegral_of_injective {R S : Type*} [CommRing R] [CommRing S]
    [Algebra R S] [Algebra.IsIntegral R S] (hinj : Function.Injective (algebraMap R S)) :
    ringKrullDim R = ringKrullDim S := by
  refine le_antisymm ?_ ?_
  · change Order.krullDim (PrimeSpectrum R) ≤ Order.krullDim (PrimeSpectrum S)
    refine iSup_le fun l => ?_
    obtain ⟨L, hlen, -⟩ := exists_ltSeries_comap_eq_last hinj l
    rw [← hlen]
    exact Order.LTSeries.length_le_krullDim L
  · change Order.krullDim (PrimeSpectrum S) ≤ Order.krullDim (PrimeSpectrum R)
    refine Order.krullDim_le_of_strictMono (PrimeSpectrum.comap (algebraMap R S)) ?_
    intro q1 q2 hlt
    rw [← PrimeSpectrum.asIdeal_lt_asIdeal]
    obtain ⟨y, hy2, hy1⟩ := SetLike.exists_of_lt ((PrimeSpectrum.asIdeal_lt_asIdeal _ _).mpr hlt)
    exact Ideal.comap_lt_comap_of_integral_mem_sdiff
      ((PrimeSpectrum.asIdeal_le_asIdeal _ _).mpr hlt.le) ⟨hy2, hy1⟩
      (Algebra.IsIntegral.isIntegral y)

theorem height_le_height_under_of_isIntegral {R S : Type*} [CommRing R] [CommRing S]
    [Algebra R S] [Algebra.IsIntegral R S] (P : Ideal S) [P.IsPrime] :
    P.height ≤ (P.under R).height := by
  haveI : (P.under R).IsPrime := inferInstance
  rw [show P.height = Order.height (⟨P, ‹_›⟩ : PrimeSpectrum S) from
      PrimeSpectrum.height_eq_orderHeight ⟨P, _⟩,
    show (P.under R).height = Order.height (⟨P.under R, ‹_›⟩ : PrimeSpectrum R) from
      PrimeSpectrum.height_eq_orderHeight ⟨P.under R, _⟩]
  have hf : StrictMono (PrimeSpectrum.comap (algebraMap R S)) := by
    intro q1 q2 hlt
    rw [← PrimeSpectrum.asIdeal_lt_asIdeal]
    obtain ⟨y, hy2, hy1⟩ := SetLike.exists_of_lt ((PrimeSpectrum.asIdeal_lt_asIdeal _ _).mpr hlt)
    exact Ideal.comap_lt_comap_of_integral_mem_sdiff
      ((PrimeSpectrum.asIdeal_le_asIdeal _ _).mpr hlt.le) ⟨hy2, hy1⟩
      (Algebra.IsIntegral.isIntegral y)
  exact Order.height_le_height_apply_of_strictMono _ hf ⟨P, ‹_›⟩

theorem height_eq_height_under_of_hasGoingDown {R S : Type*} [CommRing R] [CommRing S]
    [IsNoetherianRing R] [IsNoetherianRing S] [Algebra R S] [Algebra.IsIntegral R S] [Algebra.HasGoingDown R S]
    (P : Ideal S) [P.IsPrime] : P.height = (P.under R).height := by
  refine le_antisymm (height_le_height_under_of_isIntegral P) ?_
  rw [Ideal.height_eq_height_add_of_liesOver_of_hasGoingDown (P.under R) P]
  exact le_self_add

theorem ringKrullDim_mvPolynomial_fin (k : Type u) [Field k] (s : ℕ) :
    ringKrullDim (MvPolynomial (Fin s) k) = s := by
  rw [MvPolynomial.ringKrullDim_of_isNoetherianRing, ringKrullDim_eq_zero_of_field, zero_add,
    Nat.card_eq_fintype_card, Fintype.card_fin]

theorem height_eq_of_isMaximal_mvPolynomial (k : Type u) [Field k] :
    ∀ (n : ℕ) (M : Ideal (MvPolynomial (Fin n) k)), M.IsMaximal → M.height = n := by
  intro n
  induction n with
  | zero =>
    intro M hM
    have hle : (M.height : WithBot ℕ∞) ≤ ringKrullDim (MvPolynomial (Fin 0) k) :=
      Ideal.height_le_ringKrullDim_of_ne_top hM.ne_top
    rw [ringKrullDim_mvPolynomial_fin] at hle
    have : M.height ≤ 0 := by exact_mod_cast hle
    simpa using this
  | succ n ih =>
    intro M hM
    haveI := hM
    let e : MvPolynomial (Fin (n + 1)) k ≃+* (MvPolynomial (Fin n) k)[X] :=
      (MvPolynomial.finSuccEquiv k n).toRingEquiv
    let M' : Ideal (MvPolynomial (Fin n) k)[X] := M.map e
    haveI hM' : M'.IsMaximal := Ideal.map_isMaximal_of_equiv e
    let p : Ideal (MvPolynomial (Fin n) k) := M'.under (MvPolynomial (Fin n) k)
    haveI : M'.LiesOver p := ⟨rfl⟩
    have hp : p.IsMaximal := by
      have : p = M'.comap (C : MvPolynomial (Fin n) k →+* (MvPolynomial (Fin n) k)[X]) := by
        simp only [p, Ideal.under_def, Polynomial.algebraMap_eq]
      rw [this]
      exact Polynomial.isMaximal_comap_C_of_isJacobsonRing M'
    have h1 : M'.height = p.height + 1 := Polynomial.height_eq_height_add_one p M'
    have h2 : p.height = n := ih p hp
    have h3 : M'.height = M.height := RingEquiv.height_map e M
    rw [← h3, h1, h2]
    norm_cast

theorem height_eq_ringKrullDim_of_isMaximal (k : Type u) {A : Type v} [Field k] [CommRing A]
    [IsDomain A] [Algebra k A] [Algebra.FiniteType k A] (m : Ideal A) [hm : m.IsMaximal] :
    (m.height : WithBot ℕ∞) = ringKrullDim A := by
  obtain ⟨s, g, hinj, hfin⟩ := exists_finite_inj_algHom_of_fg k A
  letI : Algebra (MvPolynomial (Fin s) k) A := g.toRingHom.toAlgebra
  have hint : g.toRingHom.IsIntegral := RingHom.Finite.to_isIntegral hfin
  haveI : Algebra.IsIntegral (MvPolynomial (Fin s) k) A := ⟨hint⟩
  haveI : FaithfulSMul (MvPolynomial (Fin s) k) A :=
    (faithfulSMul_iff_algebraMap_injective _ _).mpr hinj
  haveI : IsNoetherianRing A := Algebra.FiniteType.isNoetherianRing k A
  have hdim : ringKrullDim A = s := by
    rw [← ringKrullDim_mvPolynomial_fin k s]
    exact (ringKrullDim_eq_of_isIntegral_of_injective (R := MvPolynomial (Fin s) k) hinj).symm
  refine le_antisymm (Ideal.height_le_ringKrullDim_of_ne_top hm.ne_top) ?_
  let m' : Ideal (MvPolynomial (Fin s) k) := m.under (MvPolynomial (Fin s) k)
  have h1 : m'.height = s := height_eq_of_isMaximal_mvPolynomial k s m' inferInstance
  have h2 : m.height = m'.height + _ := Ideal.height_eq_height_add_of_liesOver_of_hasGoingDown m' m
  have h3 : (s : ℕ∞) ≤ m.height := by
    rw [h2, h1]; exact le_self_add
  rw [hdim]
  exact_mod_cast h3

end P2mDimFormula
end PhilipponMultiplicity.AffineDimensionReuse

end


section
-- Reuse of the completed affine principal-localization dimension proof.

set_option autoImplicit false
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open scoped nonZeroDivisors
noncomputable section

namespace PhilipponMultiplicity.PrincipalChartLocalizationReuse

/-- Principal localization cannot increase Krull dimension. -/
theorem localization_dimension_le
    {R : Type*} [CommRing R] (r : R) :
    ringKrullDim (Localization.Away r) ≤ ringKrullDim R := by
  apply Order.krullDim_le_of_strictMono
    (PrimeSpectrum.comap (algebraMap R (Localization.Away r)))
  intro p q hpq
  apply (PrimeSpectrum.asIdeal_lt_asIdeal _ _).mp
  exact (IsLocalization.orderEmbedding (Submonoid.powers r) (Localization.Away r)).strictMono
    ((PrimeSpectrum.asIdeal_lt_asIdeal _ _).mpr hpq)

/-- A nonempty principal open of an affine integral variety has its original
dimension. The maximal-height theorem is reused from the affine altitude proof. -/
theorem localization_dimension_eq
    (K : Type*) [Field K] {B : Type*} [CommRing B] [IsDomain B]
    [Algebra K B] [Algebra.FiniteType K B] (r : B) (hr : r ≠ 0) :
    ringKrullDim (Localization.Away r) = ringKrullDim B := by
  let : IsDomain (Localization.Away r) := IsLocalization.Away.isDomain _ hr
  let : IsJacobsonRing B := isJacobsonRing_of_finiteType (A := K)
  let : Algebra.FiniteType K (Localization.Away r) :=
    Algebra.FiniteType.trans (inferInstance : Algebra.FiniteType K B)
      (inferInstance : Algebra.FiniteType B (Localization.Away r))
  obtain ⟨m, hm⟩ := Ideal.exists_maximal (Localization.Away r)
  let := hm
  let hmB : (m.under B).IsMaximal :=
    ((IsLocalization.isMaximal_iff_isMaximal_disjoint (Localization.Away r) r m).mp hm).1
  rw [← AffineDimensionReuse.P2mDimFormula.height_eq_ringKrullDim_of_isMaximal K m,
    ← AffineDimensionReuse.P2mDimFormula.height_eq_ringKrullDim_of_isMaximal K (m.under B),
    IsLocalization.height_under (Submonoid.powers r)]


end PhilipponMultiplicity.PrincipalChartLocalizationReuse
end

end


section
-- Reuse of the completed original-ideal inverse-equation presentation.

set_option autoImplicit false
set_option maxHeartbeats 300000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option linter.style.haveILetI false
noncomputable section

namespace PhilipponMultiplicity.PrincipalChartPresentationReuse
open Polynomial

/-- Adjoining the inverse of `h` presents the localized equation algebra as
a polynomial quotient. The original ideal is retained, without taking radicals. -/
def quotientAwayEquiv {R : Type*} [CommRing R] (I : Ideal R) (h : R) :
    ((Localization.Away h) ⧸ I.map (algebraMap R (Localization.Away h))) ≃ₐ[R]
      (Polynomial R ⧸ (I.map C ⊔ Ideal.span {C h * X - 1})) := by
  let J : Ideal (Polynomial R) := Ideal.span {C h * X - 1}
  let e := Localization.awayEquivAdjoin h
  have he : (I.map C).map (Ideal.Quotient.mk J) =
      (I.map (algebraMap R (Localization.Away h))).map e.toRingEquiv.toRingHom := by
    rw [Ideal.map_map, Ideal.map_map]
    congr 1
    ext r
    exact (e.commutes r).symm
  exact (Ideal.quotientEquivAlg _ _ e he).trans
    ((DoubleQuot.quotQuotEquivQuotSupₐ R J (I.map C)).trans
      (Ideal.quotientEquivAlgOfEq R (sup_comm J (I.map C))))


end PhilipponMultiplicity.PrincipalChartPresentationReuse
end

end


section

set_option autoImplicit false
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section

namespace PhilipponMultiplicity.PrincipalChartLocalization
open Polynomial

variable {R : Type*} [CommRing R]

abbrev Presentation (I : Ideal R) (h : R) :=
  Polynomial R ⧸ (I.map C ⊔ Ideal.span {C h * X - 1})

/-- Quotienting before or after adjoining the inverse gives the same ring. -/
def localizedQuotientEquiv (I : Ideal R) (h : R) :
    ((Localization.Away h) ⧸ I.map (algebraMap R (Localization.Away h))) ≃ₐ[R ⧸ I]
      Localization.Away (Ideal.Quotient.mk I h) := by
  let B := (Localization.Away h) ⧸ I.map (algebraMap R (Localization.Away h))
  haveI : IsLocalization.Away (Ideal.Quotient.mk I h) B := by
    have hs : Algebra.algebraMapSubmonoid (R ⧸ I) (Submonoid.powers h) =
        Submonoid.powers (Ideal.Quotient.mk I h) := by
      exact Submonoid.map_powers _ _
    rw [IsLocalization.Away, ← hs]
    infer_instance
  exact IsLocalization.algEquiv (Submonoid.powers (Ideal.Quotient.mk I h)) B _

/-- The explicit inverse-equation quotient is the principal localization
of the original quotient ring. Neither ideal is radicalized. -/
def presentationEquiv (I : Ideal R) (h : R) :
    Presentation I h ≃+* Localization.Away (Ideal.Quotient.mk I h) :=
  (PrincipalChartPresentationReuse.quotientAwayEquiv I h).symm.toRingEquiv.trans
    (localizedQuotientEquiv I h).toRingEquiv

def baseMap (I : Ideal R) (h : R) : R ⧸ I →+* Presentation I h :=
  Ideal.Quotient.lift I ((Ideal.Quotient.mk _).comp C) (by
    intro r hr
    apply Ideal.Quotient.eq_zero_iff_mem.mpr
    exact Ideal.mem_sup_left (Ideal.mem_map_of_mem C hr))

@[simp] theorem baseMap_mk (I : Ideal R) (h r : R) :
    baseMap I h (Ideal.Quotient.mk I r) =
      Ideal.Quotient.mk (I.map C ⊔ Ideal.span {C h * X - 1}) (C r) := rfl

theorem inverse_relation (I : Ideal R) (h : R) :
    baseMap I h (Ideal.Quotient.mk I h) *
      Ideal.Quotient.mk (I.map C ⊔ Ideal.span {C h * X - 1}) X = 1 := by
  have he : Ideal.Quotient.mk (I.map C ⊔ Ideal.span {C h * X - 1}) (C h * X - 1) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr
      (Ideal.mem_sup_right (Ideal.subset_span (Set.mem_singleton _)))
  exact sub_eq_zero.mp (by simpa only [map_sub, map_mul, map_one, baseMap_mk] using he)

theorem quotient_nontrivial (I : Ideal R) (h : R) [Nontrivial (Presentation I h)] :
    Nontrivial (R ⧸ I) := (baseMap I h).domain_nontrivial

theorem denominator_ne_zero (I : Ideal R) (h : R) [Nontrivial (Presentation I h)] :
    Ideal.Quotient.mk I h ≠ 0 := by
  intro hz
  have he := inverse_relation I h
  rw [hz, map_zero, zero_mul] at he
  exact zero_ne_one he

/-- A nonzero inverse-equation algebra over an affine domain is a domain of
the same Krull dimension. The nonzero denominator follows from the equations. -/
theorem domain_and_dimension (K : Type*) [Field K] [Algebra K R]
    (I : Ideal R) (h : R) [IsDomain (R ⧸ I)] [Algebra.FiniteType K (R ⧸ I)]
    [Nontrivial (Presentation I h)] :
    IsDomain (Presentation I h) ∧ ringKrullDim (Presentation I h) = ringKrullDim (R ⧸ I) := by
  have hh := denominator_ne_zero I h
  letI : IsDomain (Localization.Away (Ideal.Quotient.mk I h)) :=
    IsLocalization.Away.isDomain _ hh
  refine ⟨(presentationEquiv I h).injective.isDomain, ?_⟩
  rw [(presentationEquiv I h).ringKrullDim]
  exact PrincipalChartLocalizationReuse.localization_dimension_eq K _ hh

end PhilipponMultiplicity.PrincipalChartLocalization
end

end


section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open scoped BigOperators Topology
noncomputable section
attribute [local instance] MvPolynomial.algebraMvPolynomial
universe u

namespace PhilipponMultiplicity
open SectionThree SectionThreeSupport

theorem principal_chart_of_affine_chart
    (K : Type u) [NontriviallyNormedField K] (hK : IsPhilipponBaseField K)
    (hchart : ∀ (M : MultiProjectiveSpace K) (W : Set M.Point),
      @IsClosed _ M.zariskiTopology W → @IsIrreducible _ M.zariskiTopology W →
      ∀ b : ∀ i : M.FactorIndex, Fin (M.ambientDimension i + 1),
        let S := M.CoordinateRing ⧸
          (M.vanishingIdeal W ⊔ Ideal.span (Set.range (fun i : M.FactorIndex =>
            (MvPolynomial.X (⟨i,b i⟩ : M.Variable) : M.CoordinateRing) - 1)))
        Nontrivial S → IsDomain S ∧ ringKrullDim S = locusDimension M W) :
    ∀ (M : MultiProjectiveSpace K) (W : Set M.Point),
      @IsClosed _ M.zariskiTopology W → @IsIrreducible _ M.zariskiTopology W →
      ∀ b : ∀ i : M.FactorIndex, Fin (M.ambientDimension i + 1),
      ∀ H : M.CoordinateRing,
        let A := (Polynomial M.CoordinateRing) ⧸
          (((M.vanishingIdeal W ⊔ Ideal.span (Set.range (fun i : M.FactorIndex =>
            (MvPolynomial.X (⟨i,b i⟩ : M.Variable) : M.CoordinateRing) - 1))).map
              Polynomial.C) ⊔ Ideal.span {Polynomial.C H * Polynomial.X - 1})
        Nontrivial A → IsDomain A ∧ ringKrullDim A = locusDimension M W := by
  intro M W hW hirr b H
  dsimp only
  intro hnon
  let I : Ideal M.CoordinateRing := M.vanishingIdeal W ⊔
    Ideal.span (Set.range (fun i : M.FactorIndex =>
      (MvPolynomial.X (⟨i,b i⟩ : M.Variable) : M.CoordinateRing) - 1))
  change Nontrivial (PrincipalChartLocalization.Presentation I H) at hnon
  letI := hnon
  have hS := PrincipalChartLocalization.quotient_nontrivial I H
  obtain ⟨hdom, hdim⟩ := hchart M W hW hirr b hS
  letI : IsDomain (M.CoordinateRing ⧸ I) := hdom
  haveI : Algebra.FiniteType K (M.CoordinateRing ⧸ I) := inferInstance
  obtain ⟨hA, heq⟩ := PrincipalChartLocalization.domain_and_dimension K I H
  exact ⟨hA, heq.trans hdim⟩

end PhilipponMultiplicity
end

end

set_option autoImplicit false
open PhilipponMultiplicity PhilipponMultiplicity.SectionThree PhilipponMultiplicity.SectionThreeSupport
open scoped BigOperators Topology
attribute [local instance] MvPolynomial.algebraMvPolynomial
universe u

theorem solution
    (K : Type u) [NontriviallyNormedField K] (hK : IsPhilipponBaseField K) :
    ∀ (M : MultiProjectiveSpace K) (W : Set M.Point),
      @IsClosed _ M.zariskiTopology W → @IsIrreducible _ M.zariskiTopology W →
      ∀ b : ∀ i : M.FactorIndex, Fin (M.ambientDimension i + 1),
      ∀ H : M.CoordinateRing,
        let A := (Polynomial M.CoordinateRing) ⧸
          (((M.vanishingIdeal W ⊔ Ideal.span (Set.range (fun i : M.FactorIndex =>
            (MvPolynomial.X (⟨i,b i⟩ : M.Variable) : M.CoordinateRing) - 1))).map
              Polynomial.C) ⊔ Ideal.span {Polynomial.C H * Polynomial.X - 1})
        Nontrivial A → IsDomain A ∧ ringKrullDim A = locusDimension M W := by
  exact principal_chart_of_affine_chart K hK
    (normalized_affine_chart_domain_and_dimension K hK)
