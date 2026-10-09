-- Prove2me | solution 1 for PhilipponMultiplicity.generic_mixed_sections_finite
-- status  : ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-10-08T22:48:33.376725+00:00
-- url     : https://prove2.me/submissions/af0375c3-acae-4286-8c5c-6626bc0f2cb0

import Theorems.Thm_PhilipponMultiplicity_generic_mixed_sections_avoid_boundary
import Theorems.Thm_PhilipponMultiplicity_mixed_incidence_domain_and_dimension
import Definitions.Def_PhilipponMultiplicity_GenericMixedSections
import Definitions.Def_PhilipponMultiplicity_GeometricSupport
import Definitions.Def_PhilipponMultiplicity_UniversalMixedSlices
import Mathlib


section

/-! Reused integral-extension dimension proof from the accepted public altitude
source, submission 9f4900bf-796d-5f87-b671-c949b384b42f. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency.types false
namespace PolynomialGrowth.IntegralDimension

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


end PolynomialGrowth.IntegralDimension

end


section

set_option autoImplicit false
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open scoped BigOperators
open MvPolynomial
noncomputable section

namespace PhilipponMultiplicity.GenericIncidence
open GenericMixedSections
variable {K : Type*} [Field K] (M : MultiProjectiveSpace K)
    (l : List M.FactorIndex)

/-- Reorder the coefficient and ambient variables and adjoin the inverse
variable used by the established mixed-incidence presentation. -/
def toTotal : UniversalRing M l →+* MixedFamily.TotalPolynomial M l :=
  eval₂Hom (map (Polynomial.C.comp C)) (fun v => MixedFamily.fixed M l (X v))

/-- The principal chart parameter is one, so its inverse variable is one. -/
def fromTotal : MixedFamily.TotalPolynomial M l →+* UniversalRing M l :=
  eval₂Hom (Polynomial.eval₂RingHom (map C) 1) (fun t => C (X t))

@[simp] theorem toTotal_C (r : CoeffRing M l) :
    toTotal M l (C r) = map (Polynomial.C.comp C) r := eval₂Hom_C _ _ _

@[simp] theorem toTotal_X (v : M.Variable) :
    toTotal M l (X v) = MixedFamily.fixed M l (X v) := eval₂Hom_X' _ _ _

@[simp] theorem fromTotal_C (P : Polynomial M.CoordinateRing) :
    fromTotal M l (C P) = Polynomial.eval₂RingHom (map C) 1 P := eval₂Hom_C _ _ _

@[simp] theorem fromTotal_X (t : Fin l.length × M.Variable) :
    fromTotal M l (X t) = C (X t) := eval₂Hom_X' _ _ _

@[simp] theorem fromTotal_fixed (P : M.CoordinateRing) :
    fromTotal M l (MixedFamily.fixed M l P) = map C P := by
  simp [MixedFamily.fixed, Polynomial.eval₂_C]

@[simp] theorem fromTotal_coeff (r : CoeffRing M l) :
    fromTotal M l (map (Polynomial.C.comp C) r) = C r := by
  induction r using MvPolynomial.induction_on with
  | C a => simp [Polynomial.eval₂_C]
  | add p q hp hq => simp [hp, hq]
  | mul_X p i hp => simp [hp]

@[simp] theorem toTotal_fixed (P : M.CoordinateRing) :
    toTotal M l (map C P) = MixedFamily.fixed M l P := by
  induction P using MvPolynomial.induction_on with
  | C a => simp [MixedFamily.fixed]
  | add p q hp hq => simp [hp, hq]
  | mul_X p i hp => simp [hp]

@[simp] theorem toTotal_row (j : Fin l.length) :
    toTotal M l (universalRow M l j) = MixedFamily.row M l j := by
  simp [universalRow, MixedFamily.row]

@[simp] theorem fromTotal_row (j : Fin l.length) :
    fromTotal M l (MixedFamily.row M l j) = universalRow M l j := by
  simp [universalRow, MixedFamily.row]

theorem fromTotal_toTotal :
    (fromTotal M l).comp (toTotal M l) = RingHom.id _ := by
  apply MvPolynomial.ringHom_ext
  · intro r
    simp
  · intro v
    simp

variable (W : Set M.Point)
    (b : ∀ i : M.FactorIndex, Fin (M.ambientDimension i + 1))

/-- Every original normalized equation maps into the actual incidence ideal. -/
theorem normalized_le_comap :
    normalizedIdeal M l W b ≤
      (MixedFamily.ideal M W l b 1).comap (toTotal M l) := by
  let J := MixedFamily.ideal M W l b 1
  have hbase (P : M.CoordinateRing) (hP : P ∈ M.vanishingIdeal W) :
      MixedFamily.fixed M l P ∈ J := by
    apply Ideal.mem_sup_left
    apply Ideal.mem_sup_left
    apply Ideal.mem_sup_left
    exact Ideal.mem_map_of_mem _ hP
  have hrow (j : Fin l.length) : MixedFamily.row M l j ∈ J := by
    apply Ideal.mem_sup_left
    apply Ideal.mem_sup_left
    apply Ideal.mem_sup_right
    have hle : Ideal.span {MixedFamily.row M l j} ≤
        ⨆ k : Fin l.length, ⨆ (_ : k.val < l.length),
          Ideal.span {MixedFamily.row M l k} :=
      le_iSup_of_le j (le_iSup_of_le j.isLt le_rfl)
    exact hle (Ideal.subset_span (Set.mem_singleton _))
  have hpivot (i : M.FactorIndex) :
      MixedFamily.fixed M l (X (⟨i,b i⟩ : M.Variable) - 1) ∈ J := by
    apply Ideal.mem_sup_left
    apply Ideal.mem_sup_right
    exact Ideal.mem_map_of_mem _ (Ideal.subset_span (Set.mem_range_self i))
  apply sup_le
  · apply sup_le
    · apply Ideal.map_le_iff_le_comap.mpr
      intro P hP
      change toTotal M l (map C P) ∈ J
      simpa only [toTotal_fixed] using hbase P hP
    · refine iSup_le fun j => Ideal.span_le.mpr ?_
      rintro P rfl
      change toTotal M l (universalRow M l j) ∈ J
      simpa only [toTotal_row] using hrow j
  · apply Ideal.span_le.mpr
    rintro P ⟨i,rfl⟩
    change toTotal M l (X (⟨i,b i⟩ : M.Variable) - 1) ∈ J
    simpa only [map_sub, map_one, toTotal_X] using hpivot i

/-- Evaluating the added inverse at one preserves every incidence relation. -/
theorem total_le_comap :
    MixedFamily.ideal M W l b 1 ≤
      (normalizedIdeal M l W b).comap (fromTotal M l) := by
  let I := normalizedIdeal M l W b
  apply sup_le
  · apply sup_le
    · apply sup_le
      · apply Ideal.map_le_iff_le_comap.mpr
        intro P hP
        change fromTotal M l (MixedFamily.fixed M l P) ∈ I
        rw [fromTotal_fixed]
        exact Ideal.mem_sup_left (Ideal.mem_sup_left (Ideal.mem_map_of_mem _ hP))
      · refine iSup_le fun j => iSup_le fun _ => Ideal.span_le.mpr ?_
        rintro P rfl
        change fromTotal M l (MixedFamily.row M l j) ∈ I
        rw [fromTotal_row]
        apply Ideal.mem_sup_left
        apply Ideal.mem_sup_right
        have hle : Ideal.span {universalRow M l j} ≤
            ⨆ k : Fin l.length, Ideal.span {universalRow M l k} :=
          le_iSup_of_le j le_rfl
        exact hle (Ideal.subset_span (Set.mem_singleton _))
    · apply Ideal.map_le_iff_le_comap.mpr
      apply Ideal.span_le.mpr
      rintro P ⟨i,rfl⟩
      change fromTotal M l (MixedFamily.fixed M l (X (⟨i,b i⟩ : M.Variable) - 1)) ∈ I
      rw [fromTotal_fixed]
      rw [map_sub, map_one, map_X]
      exact Ideal.mem_sup_right (Ideal.subset_span (Set.mem_range_self i))
  · apply Ideal.span_le.mpr
    rintro P rfl
    change fromTotal M l (C (Polynomial.C 1 * Polynomial.X - 1)) ∈ I
    simp [Polynomial.eval₂_X]

def quotientToTotal :
    UniversalRing M l ⧸ normalizedIdeal M l W b →+*
      MixedFamily.CoordinateRing M W l b 1 :=
  Ideal.quotientMap _ (toTotal M l) (normalized_le_comap M l W b)

def quotientFromTotal : MixedFamily.CoordinateRing M W l b 1 →+*
    UniversalRing M l ⧸ normalizedIdeal M l W b :=
  Ideal.quotientMap _ (fromTotal M l) (total_le_comap M l W b)

theorem quotient_leftInverse :
    Function.LeftInverse (quotientFromTotal M l W b) (quotientToTotal M l W b) := by
  intro x
  obtain ⟨P,rfl⟩ := Ideal.Quotient.mk_surjective x
  change Ideal.Quotient.mk _ (fromTotal M l (toTotal M l P)) = _
  have h := RingHom.congr_fun (fromTotal_toTotal M l) P
  simpa only [RingHom.comp_apply, RingHom.id_apply] using
    congrArg (Ideal.Quotient.mk (normalizedIdeal M l W b)) h

/-- Domain structure of the established incidence presentation transfers to
the coefficient-first normalized quotient, including its nilpotents. -/
theorem normalized_isReduced_of_incidence
    (h : Nontrivial (MixedFamily.CoordinateRing M W l b 1) →
      IsDomain (MixedFamily.CoordinateRing M W l b 1)) :
    IsReduced (UniversalRing M l ⧸ normalizedIdeal M l W b) := by
  classical
  cases subsingleton_or_nontrivial (UniversalRing M l ⧸ normalizedIdeal M l W b) with
  | inl hs => let := hs; infer_instance
  | inr hn =>
    let := hn
    let hnon := (quotientFromTotal M l W b).domain_nontrivial
    let := h hnon
    exact isReduced_of_injective (quotientToTotal M l W b)
      (quotient_leftInverse M l W b).injective

end PhilipponMultiplicity.GenericIncidence
end
end


section

set_option autoImplicit false
set_option maxHeartbeats 60000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace PhilipponMultiplicity.GenericFiniteAlgebra
open MvPolynomial Algebra

/-- The dimension bound on a finite type domain bounds its transcendence degree.
The proof uses Noether normalization and invariance under integral extensions. -/
theorem trdeg_le_of_dimension {K A : Type*} [Field K] [CommRing A]
    [IsDomain A] [Algebra K A] [Algebra.FiniteType K A]
    (n : ℕ) (hdim : ringKrullDim A ≤ (n : WithBot ℕ∞)) :
    Algebra.trdeg K A ≤ (n : Cardinal) := by
  obtain ⟨r, g, hg, hfin⟩ := exists_finite_inj_algHom_of_fg K A
  let : Algebra (MvPolynomial (Fin r) K) A := g.toRingHom.toAlgebra
  let : Algebra.IsIntegral (MvPolynomial (Fin r) K) A :=
    ⟨RingHom.Finite.to_isIntegral hfin⟩
  let : FaithfulSMul (MvPolynomial (Fin r) K) A :=
    (faithfulSMul_iff_algebraMap_injective _ _).mpr hg
  have : IsScalarTower K (MvPolynomial (Fin r) K) A :=
    IsScalarTower.of_algebraMap_eq fun k => (g.commutes k).symm
  have hr : ringKrullDim A = (r : WithBot ℕ∞) := by
    have heq := PolynomialGrowth.IntegralDimension.ringKrullDim_eq_of_isIntegral_of_injective
      (R := MvPolynomial (Fin r) K) (S := A) hg
    rw [← heq,
      MvPolynomial.ringKrullDim_of_isNoetherianRing,
      ringKrullDim_eq_zero_of_field, zero_add, Nat.card_eq_fintype_card, Fintype.card_fin]
  have htr := lift_trdeg_add_eq K (MvPolynomial (Fin r) K) A
  let : Algebra.IsAlgebraic (MvPolynomial (Fin r) K) A :=
    ⟨fun x => (Algebra.IsIntegral.isIntegral x).isAlgebraic⟩
  have hzero : Algebra.trdeg (MvPolynomial (Fin r) K) A = 0 := trdeg_eq_zero
  rw [hzero, Cardinal.lift_zero, add_zero, MvPolynomial.trdeg_of_isDomain] at htr
  simp only [Cardinal.mk_fin, Cardinal.lift_natCast] at htr
  have hrn : r ≤ n := by exact_mod_cast (hr ▸ hdim)
  exact Cardinal.lift_le.mp (htr.symm.trans_le (by
    rw [Cardinal.lift_natCast]
    exact_mod_cast hrn))

/-- Independent coefficient parameters of full dimension leave an algebraic
extension. No assumption about dominance is hidden in the dimension argument. -/
theorem isAlgebraic_of_dimension {K A ι : Type*} [Field K] [CommRing A]
    [IsDomain A] [Algebra K A] [Algebra.FiniteType K A] [Finite ι]
    [Algebra (MvPolynomial ι K) A] [IsScalarTower K (MvPolynomial ι K) A]
    [FaithfulSMul (MvPolynomial ι K) A]
    (hdim : ringKrullDim A ≤ (Nat.card ι : WithBot ℕ∞)) :
    Algebra.IsAlgebraic (MvPolynomial ι K) A := by
  let := Fintype.ofFinite ι
  have hbound := trdeg_le_of_dimension (K := K) (Nat.card ι) hdim
  have h := lift_trdeg_add_le (R := K) (S := MvPolynomial ι K) (A := A)
  rw [MvPolynomial.trdeg_of_isDomain] at h
  simp only [Cardinal.mk_fintype, ← Nat.card_eq_fintype_card,
    Cardinal.lift_natCast] at h
  have hz : Cardinal.lift (Algebra.trdeg (MvPolynomial ι K) A) = 0 := by
    apply le_antisymm _ zero_le
    apply (Cardinal.add_le_add_iff_of_lt_aleph0 Cardinal.natCast_lt_aleph0).mp
    simpa [add_comm] using h.trans (Cardinal.lift_le.mpr hbound)
  exact trdeg_eq_zero_iff.mp (by simpa using hz)

end PhilipponMultiplicity.GenericFiniteAlgebra

end
end


section

set_option autoImplicit false
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace PhilipponMultiplicity.GenericFiniteAlgebra
open MvPolynomial Algebra

/-- A polynomial quotient whose domain has at most the parameter dimension
becomes finite after passage to the coefficient function field. The generic
quotient may be zero, and dominance is not assumed. -/
theorem finite_generic_quotient {K ι σ : Type*} [Field K] [Finite ι] [Finite σ]
    (I : Ideal (MvPolynomial σ (MvPolynomial ι K)))
    (hI : Nontrivial (MvPolynomial σ (MvPolynomial ι K) ⧸ I) →
      IsDomain (MvPolynomial σ (MvPolynomial ι K) ⧸ I) ∧
      ringKrullDim (MvPolynomial σ (MvPolynomial ι K) ⧸ I) ≤
        (Nat.card ι : WithBot ℕ∞)) :
    Module.Finite (FractionRing (MvPolynomial ι K))
      (MvPolynomial σ (FractionRing (MvPolynomial ι K)) ⧸
        I.map (MvPolynomial.map (algebraMap (MvPolynomial ι K)
          (FractionRing (MvPolynomial ι K))))) := by
  classical
  let R := MvPolynomial ι K
  let L := FractionRing R
  let U := MvPolynomial σ R ⧸ I
  let J := I.map (MvPolynomial.map (algebraMap R L))
  let V := MvPolynomial σ L ⧸ J
  change Module.Finite L V
  cases subsingleton_or_nontrivial V with
  | inl hs => let := hs; infer_instance
  | inr hn =>
    let := hn
    let f : U →ₐ[R] V := Ideal.quotientMapₐ J
      (MvPolynomial.mapAlgHom (Algebra.ofId R L)) (Ideal.le_comap_map)
    let hU := f.toRingHom.domain_nontrivial
    let := (hI hU).1
    have hinj : Function.Injective (algebraMap R U) := by
      intro x y hxy
      have h := congrArg f hxy
      apply IsFractionRing.injective R L
      apply (algebraMap L V).injective
      simpa only [f.commutes, IsScalarTower.algebraMap_apply R L V] using h
    let : @FaithfulSMul R U (Algebra.toSMul) :=
      (faithfulSMul_iff_algebraMap_injective R U).mpr hinj
    let : Algebra.IsAlgebraic R U :=
      isAlgebraic_of_dimension (K := K) (A := U) (ι := ι) (hI hU).2
    have hx (i : σ) : IsIntegral L (Ideal.Quotient.mk J (X i)) := by
      have hi : IsAlgebraic R (f (Ideal.Quotient.mk I (X i))) :=
        (Algebra.IsAlgebraic.isAlgebraic (R := R) (Ideal.Quotient.mk I (X i))).algHom f
      have hiL : IsAlgebraic L (f (Ideal.Quotient.mk I (X i))) :=
        IsAlgebraic.extendScalars (R := R) (S := L) (A := V)
          (IsFractionRing.injective R L) hi
      have hfx : f (Ideal.Quotient.mk I (X i)) = Ideal.Quotient.mk J (X i) := by
        change Ideal.Quotient.mk J (MvPolynomial.map (algebraMap R L) (X i)) = _
        rw [MvPolynomial.map_X]
      rw [hfx] at hiL
      exact hiL.isIntegral
    have : Algebra.IsIntegral L V := by
      constructor
      intro x
      obtain ⟨P,rfl⟩ := Ideal.Quotient.mk_surjective x
      induction P using MvPolynomial.induction_on with
      | C a => exact isIntegral_algebraMap
      | add p q hp hq =>
        rw [map_add]
        exact IsIntegral.add (R := L) (A := V) hp hq
      | mul_X p i hp =>
        rw [map_mul]
        exact IsIntegral.mul (R := L) (A := V) hp (hx i)
    exact Algebra.IsIntegral.finite (R := L) (A := V)

end PhilipponMultiplicity.GenericFiniteAlgebra

end
end


section

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace PhilipponMultiplicity.GenericIncidence
open GenericMixedSections

/-- Transfer the established incidence dimension to the normalized quotient
and apply the coefficient-field finiteness theorem. -/
theorem generic_normalized_finite {K : Type*} [Field K]
    (M : MultiProjectiveSpace K) (W : Set M.Point) (l : List M.FactorIndex)
    (b : ∀ i : M.FactorIndex, Fin (M.ambientDimension i + 1))
    (h : Nontrivial (MixedFamily.CoordinateRing M W l b 1) →
      IsDomain (MixedFamily.CoordinateRing M W l b 1) ∧
      ringKrullDim (MixedFamily.CoordinateRing M W l b 1) =
        Nat.card (Fin l.length × M.Variable)) :
    Module.Finite (FractionRing (CoeffRing M l))
      (MvPolynomial M.Variable (FractionRing (CoeffRing M l)) ⧸
        (normalizedIdeal M l W b).map (genericMap M l)) := by
  apply GenericFiniteAlgebra.finite_generic_quotient
  intro hn
  let := hn
  have hnon := (quotientFromTotal M l W b).domain_nontrivial
  obtain ⟨hdom,hdim⟩ := h hnon
  let := hdom
  refine ⟨(quotient_leftInverse M l W b).injective.isDomain _, ?_⟩
  rw [← hdim]
  exact ringKrullDim_le_of_surjective (quotientFromTotal M l W b)
    (quotient_leftInverse M l W b).surjective

end PhilipponMultiplicity.GenericIncidence

end
end


section

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open scoped BigOperators Topology
noncomputable section
namespace PhilipponMultiplicity
open SectionThree SectionThreeSupport
namespace GenericIncidence

/-- Finiteness is now proved from the existing incidence theorem; only
avoidance of the prescribed boundary is an Open geometric input. -/
theorem finite_of_boundary
    (K : Type*) [NontriviallyNormedField K] (hK : IsPhilipponBaseField K)
    (hincidence : ∀ (M : MultiProjectiveSpace K) (W : Set M.Point),
      @IsClosed _ M.zariskiTopology W → @IsIrreducible _ M.zariskiTopology W →
      ∀ (α : M.FactorIndex → ℕ), (∀ i, α i ≤ M.ambientDimension i) →
      (∑ i, α i = locusDimension M W) →
      ∀ l : List M.FactorIndex, (∀ i, l.count i = α i) →
      ∀ b : ∀ i : M.FactorIndex, Fin (M.ambientDimension i + 1),
      ∀ H : M.CoordinateRing,
        Nontrivial (MixedFamily.CoordinateRing M W l b H) →
        IsDomain (MixedFamily.CoordinateRing M W l b H) ∧
        ringKrullDim (MixedFamily.CoordinateRing M W l b H) =
          Nat.card (Fin l.length × M.Variable))
    (hboundary : ∀ (M : MultiProjectiveSpace K) (W : Set M.Point),
      @IsClosed _ M.zariskiTopology W → @IsIrreducible _ M.zariskiTopology W →
      ∀ (α : M.FactorIndex → ℕ), (∀ i, α i ≤ M.ambientDimension i) →
      (∑ i, α i = locusDimension M W) →
      ∀ B : Set M.Point, @IsClosed _ M.zariskiTopology B → B ⊆ W →
      (W \ B).Nonempty →
      ∀ l : List M.FactorIndex, (∀ i, l.count i = α i) →
        ∀ b : ∀ i : M.FactorIndex, Fin (M.ambientDimension i + 1),
          (GenericMixedSections.normalizedIdeal M l B b).map
            (GenericMixedSections.genericMap M l) = ⊤) :
    ∀ (M : MultiProjectiveSpace K) (W : Set M.Point),
      @IsClosed _ M.zariskiTopology W → @IsIrreducible _ M.zariskiTopology W →
      ∀ (α : M.FactorIndex → ℕ), (∀ i, α i ≤ M.ambientDimension i) →
      (∑ i, α i = locusDimension M W) →
      ∀ B : Set M.Point, @IsClosed _ M.zariskiTopology B → B ⊆ W →
      (W \ B).Nonempty →
      ∀ l : List M.FactorIndex, (∀ i, l.count i = α i) →
        ∀ b : ∀ i : M.FactorIndex, Fin (M.ambientDimension i + 1),
          Module.Finite (FractionRing (GenericMixedSections.CoeffRing M l))
            (MvPolynomial M.Variable (FractionRing (GenericMixedSections.CoeffRing M l)) ⧸
              (GenericMixedSections.normalizedIdeal M l W b).map
                (GenericMixedSections.genericMap M l)) ∧
          (GenericMixedSections.normalizedIdeal M l B b).map
            (GenericMixedSections.genericMap M l) = ⊤ := by
  intro M W hW hirr α hα hdim B hB hBW hnonempty l hl b
  refine ⟨?_, hboundary M W hW hirr α hα hdim B hB hBW hnonempty l hl b⟩
  exact generic_normalized_finite M W l b
    (hincidence M W hW hirr α hα hdim l hl b 1)

end GenericIncidence
end PhilipponMultiplicity
end
end

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open PhilipponMultiplicity PhilipponMultiplicity.SectionThree PhilipponMultiplicity.SectionThreeSupport
open scoped BigOperators Topology

theorem solution
    (K : Type*) [NontriviallyNormedField K] (hK : IsPhilipponBaseField K) :
    ∀ (M : MultiProjectiveSpace K) (W : Set M.Point),
      @IsClosed _ M.zariskiTopology W → @IsIrreducible _ M.zariskiTopology W →
      ∀ (α : M.FactorIndex → ℕ), (∀ i, α i ≤ M.ambientDimension i) →
      (∑ i, α i = locusDimension M W) →
      ∀ B : Set M.Point, @IsClosed _ M.zariskiTopology B → B ⊆ W →
      (W \ B).Nonempty →
      ∀ l : List M.FactorIndex, (∀ i, l.count i = α i) →
        ∀ b : ∀ i : M.FactorIndex, Fin (M.ambientDimension i + 1),
          Module.Finite (FractionRing (GenericMixedSections.CoeffRing M l))
            (MvPolynomial M.Variable (FractionRing (GenericMixedSections.CoeffRing M l)) ⧸
              (GenericMixedSections.normalizedIdeal M l W b).map
                (GenericMixedSections.genericMap M l)) ∧
          (GenericMixedSections.normalizedIdeal M l B b).map
            (GenericMixedSections.genericMap M l) = ⊤ := by
  exact GenericIncidence.finite_of_boundary K hK
    (mixed_incidence_domain_and_dimension K hK)
    (generic_mixed_sections_avoid_boundary K hK)
