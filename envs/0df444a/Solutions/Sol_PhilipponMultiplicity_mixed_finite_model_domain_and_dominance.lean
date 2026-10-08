-- Prove2me | solution 1 for PhilipponMultiplicity.mixed_finite_model_domain_and_dominance
-- status  : ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-10-08T05:12:13.633455+00:00
-- url     : https://prove2.me/submissions/2ce517e3-58eb-4bfa-a5c4-ec2f2f41b0f9

import Theorems.Thm_PhilipponMultiplicity_mixed_incidence_domain_and_dimension
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

set_option autoImplicit false
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open scoped nonZeroDivisors
noncomputable section

namespace PhilipponMultiplicity.FiniteModelDominance

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

/-- If an integral algebra kills a nonzero divisor, its dimension is at least
one less than that of the source. No injectivity is assumed here. -/
theorem integral_dimension_drop
    {C D : Type*} [CommRing C] [CommRing D] [Algebra C D]
    [Algebra.IsIntegral C D] (x : C) (hx : x ∈ C⁰)
    (hzero : algebraMap C D x = 0) :
    ringKrullDim D + 1 ≤ ringKrullDim C := by
  let f : PrimeSpectrum D → PrimeSpectrum.zeroLocus (R := C) (Ideal.span {x}) :=
    fun q => ⟨PrimeSpectrum.comap (algebraMap C D) q, by
      rw [PrimeSpectrum.mem_zeroLocus]
      change Ideal.span {x} ≤ q.asIdeal.comap (algebraMap C D)
      rw [Ideal.span_singleton_le_iff_mem]
      change algebraMap C D x ∈ q.asIdeal
      rw [hzero]
      exact q.asIdeal.zero_mem⟩
  have hf : StrictMono f := by
    intro p q hpq
    change PrimeSpectrum.comap (algebraMap C D) p < PrimeSpectrum.comap (algebraMap C D) q
    rw [← PrimeSpectrum.asIdeal_lt_asIdeal]
    obtain ⟨y, hyq, hyp⟩ := SetLike.exists_of_lt ((PrimeSpectrum.asIdeal_lt_asIdeal _ _).mpr hpq)
    exact Ideal.comap_lt_comap_of_integral_mem_sdiff
      ((PrimeSpectrum.asIdeal_le_asIdeal _ _).mpr hpq.le) ⟨hyq, hyp⟩
      (Algebra.IsIntegral.isIntegral y)
  have hdim : ringKrullDim D ≤ ringKrullDim (C ⧸ Ideal.span {x}) := by
    rw [ringKrullDim_quotient]
    exact Order.krullDim_le_of_strictMono f hf
  exact (add_le_add hdim (le_refl 1)).trans
    (ringKrullDim_quotient_succ_le_of_nonZeroDivisor hx)

/-- A finite local model of full source dimension forces dominance. -/
theorem injective_of_finite_model_of_dimension
    (K : Type*) [Field K]
    {C B : Type*} [CommRing C] [IsDomain C] [CommRing B] [IsDomain B]
    [Algebra K C] [Algebra K B] [Algebra C B] [IsScalarTower K C B]
    [Algebra.FiniteType K B]
    (n : ℕ) (hC : ringKrullDim C = n) (hB : ringKrullDim B = n)
    (D : Subalgebra C B) [Module.Finite C D] (r : D) (hr : r.val ≠ 0)
    (hbij : Function.Bijective (Localization.awayMap D.val.toRingHom r)) :
    Function.Injective (algebraMap C B) := by
  rw [injective_iff_map_eq_zero]
  intro x hx
  by_contra hx0
  have hzero : algebraMap C D x = 0 := Subtype.ext hx
  have hdrop := integral_dimension_drop x (mem_nonZeroDivisors_of_ne_zero hx0) hzero
  have hloc : ringKrullDim (Localization.Away r.val) = ringKrullDim (Localization.Away r) :=
    (ringKrullDim_eq_of_ringEquiv (RingEquiv.ofBijective _ hbij)).symm
  have hle : ringKrullDim B ≤ ringKrullDim D := by
    rw [← localization_dimension_eq K r.val hr, hloc]
    exact localization_dimension_le r
  have hbad : (n : WithBot ℕ∞) + 1 ≤ n := by
    calc
      (n : WithBot ℕ∞) + 1 = ringKrullDim B + 1 := by rw [hB]
      _ ≤ ringKrullDim D + 1 := add_le_add hle (le_refl 1)
      _ ≤ ringKrullDim C := hdrop
      _ = n := hC
  have : n + 1 ≤ n := by exact_mod_cast hbad
  omega

attribute [local instance] MvPolynomial.algebraMvPolynomial

/-- Specialization of the dimension criterion to the actual coefficient ring. -/
theorem mixed_finite_model_injective
    {K : Type*} [Field K] (M : MultiProjectiveSpace K) (W : Set M.Point)
    (l : List M.FactorIndex)
    (b : ∀ i : M.FactorIndex, Fin (M.ambientDimension i + 1))
    (H : M.CoordinateRing)
    (hdom : IsDomain (MixedFamily.CoordinateRing M W l b H))
    (hdim : ringKrullDim (MixedFamily.CoordinateRing M W l b H) =
      Nat.card (Fin l.length × M.Variable))
    (D : Subalgebra (MixedFamily.ParameterRing M l) (MixedFamily.CoordinateRing M W l b H))
    (hD : Module.Finite (MixedFamily.ParameterRing M l) D)
    (r : D) (hr : r.val ≠ 0)
    (hbij : Function.Bijective (Localization.awayMap D.val.toRingHom r)) :
    Function.Injective (algebraMap (MixedFamily.ParameterRing M l)
      (MixedFamily.CoordinateRing M W l b H)) := by
  let := hdom
  let := hD
  apply injective_of_finite_model_of_dimension K (Nat.card (Fin l.length × M.Variable))
    ?_ hdim D r hr hbij
  change ringKrullDim (MvPolynomial (Fin l.length × M.Variable) K) = _
  rw [MvPolynomial.ringKrullDim_of_isNoetherianRing, ringKrullDim_eq_zero_of_field, zero_add]

end PhilipponMultiplicity.FiniteModelDominance
end

end


section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open scoped BigOperators Topology
noncomputable section
attribute [local instance] MvPolynomial.algebraMvPolynomial

namespace PhilipponMultiplicity
open SectionThree SectionThreeSupport

theorem mixed_dominance_of_incidence_dimension
    (K : Type*) [NontriviallyNormedField K] (hK : IsPhilipponBaseField K)
    (hgeometry : ∀ (M : MultiProjectiveSpace K) (W : Set M.Point),
      @IsClosed _ M.zariskiTopology W → @IsIrreducible _ M.zariskiTopology W →
      ∀ (α : M.FactorIndex → ℕ), (∀ i, α i ≤ M.ambientDimension i) →
      (∑ i, α i = locusDimension M W) →
      ∀ l : List M.FactorIndex, (∀ i, l.count i = α i) →
      ∀ b : ∀ i : M.FactorIndex, Fin (M.ambientDimension i + 1),
      ∀ H : M.CoordinateRing,
        Nontrivial (MixedFamily.CoordinateRing M W l b H) →
        IsDomain (MixedFamily.CoordinateRing M W l b H) ∧
        ringKrullDim (MixedFamily.CoordinateRing M W l b H) =
          Nat.card (Fin l.length × M.Variable)) :
    ∀ (M : MultiProjectiveSpace K) (W : Set M.Point),
      @IsClosed _ M.zariskiTopology W → @IsIrreducible _ M.zariskiTopology W →
      ∀ (α : M.FactorIndex → ℕ), (∀ i, α i ≤ M.ambientDimension i) →
      (∑ i, α i = locusDimension M W) →
      ∀ l : List M.FactorIndex, (∀ i, l.count i = α i) →
      ∀ b : ∀ i : M.FactorIndex, Fin (M.ambientDimension i + 1),
      ∀ H : M.CoordinateRing,
      ∀ D : Subalgebra (MixedFamily.ParameterRing M l) (MixedFamily.CoordinateRing M W l b H),
        Module.Finite (MixedFamily.ParameterRing M l) D →
        ∀ r : D, r.val ≠ 0 →
          Function.Bijective (Localization.awayMap D.val.toRingHom r) →
          IsDomain (MixedFamily.CoordinateRing M W l b H) ∧
          Function.Injective (algebraMap (MixedFamily.ParameterRing M l)
            (MixedFamily.CoordinateRing M W l b H)) := by
  intro M W hW hirr α hα hdim l hl b H D hD r hr hbij
  have hnon : Nontrivial (MixedFamily.CoordinateRing M W l b H) :=
    nontrivial_of_ne r.val 0 hr
  obtain ⟨hdom,hBdim⟩ := hgeometry M W hW hirr α hα hdim l hl b H hnon
  exact ⟨hdom, FiniteModelDominance.mixed_finite_model_injective
    M W l b H hdom hBdim D hD r hr hbij⟩

end PhilipponMultiplicity
end

end

set_option autoImplicit false
open PhilipponMultiplicity PhilipponMultiplicity.SectionThree PhilipponMultiplicity.SectionThreeSupport
open scoped BigOperators Topology
attribute [local instance] MvPolynomial.algebraMvPolynomial

theorem solution
    (K : Type*) [NontriviallyNormedField K] (hK : IsPhilipponBaseField K) :
    ∀ (M : MultiProjectiveSpace K) (W : Set M.Point),
      @IsClosed _ M.zariskiTopology W → @IsIrreducible _ M.zariskiTopology W →
      ∀ (α : M.FactorIndex → ℕ), (∀ i, α i ≤ M.ambientDimension i) →
      (∑ i, α i = locusDimension M W) →
      ∀ l : List M.FactorIndex, (∀ i, l.count i = α i) →
      ∀ b : ∀ i : M.FactorIndex, Fin (M.ambientDimension i + 1),
      ∀ H : M.CoordinateRing,
      ∀ D : Subalgebra (MixedFamily.ParameterRing M l) (MixedFamily.CoordinateRing M W l b H),
        Module.Finite (MixedFamily.ParameterRing M l) D →
        ∀ r : D, r.val ≠ 0 →
          Function.Bijective (Localization.awayMap D.val.toRingHom r) →
          IsDomain (MixedFamily.CoordinateRing M W l b H) ∧
          Function.Injective (algebraMap (MixedFamily.ParameterRing M l)
            (MixedFamily.CoordinateRing M W l b H)) := by
  exact mixed_dominance_of_incidence_dimension K hK
    (mixed_incidence_domain_and_dimension K hK)
