-- Prove2me | solution 1 for PhilipponMultiplicity.generic_mixed_sections_avoid_boundary
-- status  : ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-10-08T23:06:00.067187+00:00
-- url     : https://prove2.me/submissions/1365b0db-6efd-4c61-a88f-fbd2a64f0ea9

import Theorems.Thm_PhilipponMultiplicity_mixed_incidence_domain_and_dimension
import Definitions.Def_PhilipponMultiplicity_Degree
import Definitions.Def_PhilipponMultiplicity_GenericMixedSections
import Definitions.Def_PhilipponMultiplicity_GeometricSupport
import Definitions.Def_PhilipponMultiplicity_HilbertGrowth
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
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open scoped BigOperators
open MvPolynomial
noncomputable section

namespace PhilipponMultiplicity.MultiProjectiveSpace
variable {K : Type*} [Field K] (M : MultiProjectiveSpace K)

theorem IsHomogeneous.mul {P Q : M.CoordinateRing} {D E : M.FactorIndex → ℕ}
    (hP : M.IsHomogeneous P D) (hQ : M.IsHomogeneous Q E) :
    M.IsHomogeneous (P * Q) (D + E) := by
  classical
  intro d hd i
  obtain ⟨a, ha, b, hb, rfl⟩ := Finset.mem_add.mp (MvPolynomial.support_mul P Q hd)
  simpa only [Finsupp.add_apply, Finset.sum_add_distrib, Pi.add_apply, hP a ha i,
    hQ b hb i]

theorem isHomogeneous_one : M.IsHomogeneous 1 0 := by
  classical
  intro d hd i
  have hd0 : d = 0 := by simpa using hd
  simp [hd0]

theorem isOpen_basic (P : M.CoordinateRing) (D : M.FactorIndex → ℕ)
    (hP : M.IsHomogeneous P D) :
    @IsOpen _ M.zariskiTopology {x | M.eval P x ≠ 0} := by
  exact TopologicalSpace.isOpen_generateFrom_of_mem ⟨P, D, hP, rfl⟩

theorem isClosed_zero (P : M.CoordinateRing) (D : M.FactorIndex → ℕ)
    (hP : M.IsHomogeneous P D) :
    @IsClosed _ M.zariskiTopology {x | M.eval P x = 0} := by
  letI := M.zariskiTopology
  simpa only [Set.compl_setOf, not_not] using (M.isOpen_basic P D hP).isClosed_compl

theorem isTopologicalBasis_basic :
    @TopologicalSpace.IsTopologicalBasis _ M.zariskiTopology
      {U | ∃ P : M.CoordinateRing, ∃ D, M.IsHomogeneous P D ∧
        U = {x | M.eval P x ≠ 0}} := by
  classical
  letI := M.zariskiTopology
  have h := TopologicalSpace.isTopologicalBasis_of_subbasis_of_inter
    (show M.zariskiTopology = TopologicalSpace.generateFrom _ from rfl) (by
      rintro U ⟨P, D, hP, rfl⟩ V ⟨Q, E, hQ, rfl⟩
      refine ⟨P * Q, D + E, hP.mul M hQ, ?_⟩
      ext x
      simp [eval, mul_ne_zero_iff])
  have huniv : Set.univ ∈ {U | ∃ P : M.CoordinateRing, ∃ D,
      M.IsHomogeneous P D ∧ U = {x | M.eval P x ≠ 0}} := by
    refine ⟨1, 0, M.isHomogeneous_one, ?_⟩
    ext x
    simp [eval]
  simpa only [Set.insert_eq_of_mem huniv] using h

theorem eval_eq_zero_of_mem_vanishingIdeal {S : Set M.Point}
    {P : M.CoordinateRing} (hP : P ∈ M.vanishingIdeal S)
    {x : M.Point} (hx : x ∈ S) : M.eval P x = 0 := by
  have hle : M.vanishingIdeal S ≤ RingHom.ker (MvPolynomial.eval (M.coordinate x)) := by
    apply Ideal.span_le.mpr
    rintro Q ⟨_, hQ⟩
    exact hQ x hx
  exact hle hP

theorem isHomogeneous_X (v : M.Variable) :
    M.IsHomogeneous (MvPolynomial.X v) (fun i => if i = v.1 then 1 else 0) := by
  classical
  intro a ha i
  simp only [MvPolynomial.support_X, Finset.mem_singleton] at ha
  subst a
  rcases v with ⟨b, j⟩
  by_cases hi : i = b
  · subst i
    simp [Finsupp.single_apply, Sigma.mk.inj_iff]
  · have hn (k : Fin (M.ambientDimension i + 1)) :
        (⟨b, j⟩ : M.Variable) ≠ ⟨i, k⟩ := by
      intro h
      exact hi (congrArg Sigma.fst h).symm
    simp [Finsupp.single_apply, hi, hn]

theorem isHomogeneous_C (c : K) : M.IsHomogeneous (MvPolynomial.C c) 0 := by
  classical
  intro a ha i
  have ha0 : a = 0 := Finset.mem_singleton.mp (MvPolynomial.support_monomial_subset ha)
  simp [ha0]

theorem IsHomogeneous.add {P Q : M.CoordinateRing} {D : M.FactorIndex → ℕ}
    (hP : M.IsHomogeneous P D) (hQ : M.IsHomogeneous Q D) :
    M.IsHomogeneous (P + Q) D := by
  classical
  intro a ha i
  rcases Finset.mem_union.mp (MvPolynomial.support_add ha) with h | h
  · exact hP a h i
  · exact hQ a h i

theorem IsHomogeneous.neg {P : M.CoordinateRing} {D : M.FactorIndex → ℕ}
    (hP : M.IsHomogeneous P D) : M.IsHomogeneous (-P) D := by
  intro a ha i
  exact hP a (by simpa only [MvPolynomial.support_neg] using ha) i

theorem IsHomogeneous.sub {P Q : M.CoordinateRing} {D : M.FactorIndex → ℕ}
    (hP : M.IsHomogeneous P D) (hQ : M.IsHomogeneous Q D) :
    M.IsHomogeneous (P - Q) D := by
  simpa only [sub_eq_add_neg] using hP.add M (hQ.neg M)

theorem IsHomogeneous.C_mul {P : M.CoordinateRing} {D : M.FactorIndex → ℕ}
    (hP : M.IsHomogeneous P D) (c : K) : M.IsHomogeneous (MvPolynomial.C c * P) D := by
  simpa only [zero_add] using (M.isHomogeneous_C c).mul M hP

theorem IsHomogeneous.nat_mul {P : M.CoordinateRing} {D : M.FactorIndex → ℕ}
    (hP : M.IsHomogeneous P D) (c : ℕ) : M.IsHomogeneous (c * P) D := by
  simpa only [map_natCast] using hP.C_mul M (c : K)

theorem IsHomogeneous.pow {P : M.CoordinateRing} {D : M.FactorIndex → ℕ}
    (hP : M.IsHomogeneous P D) (n : ℕ) :
    M.IsHomogeneous (P ^ n) (fun i => n * D i) := by
  induction n with
  | zero =>
    convert M.isHomogeneous_one using 1
    · simp
    · funext i; simp
  | succ n ih =>
    convert ih.mul M hP using 1
    · exact pow_succ P n
    · funext i; simp [Nat.succ_mul]

theorem isHomogeneous_zero (M : MultiProjectiveSpace K) (D : M.FactorIndex → ℕ) :
    M.IsHomogeneous 0 D := by simp [IsHomogeneous]

theorem isHomogeneous_sum (M : MultiProjectiveSpace K) {ι : Type*}
    (s : Finset ι) (P : ι → M.CoordinateRing) (D : M.FactorIndex → ℕ)
    (hP : ∀ i ∈ s, M.IsHomogeneous (P i) D) :
    M.IsHomogeneous (∑ i ∈ s, P i) D := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using M.isHomogeneous_zero D
  | @insert i s hi ih =>
    simp only [Finset.sum_insert, hi, not_false_eq_true]
    exact (hP i (by simp)).add M (ih (fun j hj => hP j (by simp [hj])))

theorem isHomogeneous_prod (M : MultiProjectiveSpace K) {ι : Type*}
    (s : Finset ι) (P : ι → M.CoordinateRing) (D : ι → M.FactorIndex → ℕ)
    (hP : ∀ i ∈ s, M.IsHomogeneous (P i) (D i)) :
    M.IsHomogeneous (∏ i ∈ s, P i) (∑ i ∈ s, D i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using M.isHomogeneous_one
  | @insert i s hi ih =>
    simp only [Finset.prod_insert, Finset.sum_insert, hi, not_false_eq_true]
    exact (hP i (by simp)).mul M (ih (fun j hj => hP j (by simp [hj])))

theorem blockWeight_apply (d : M.Variable →₀ ℕ) (i : M.FactorIndex) :
    (Finsupp.weight (Hilbert.blockWeight M.factorCount M.ambientDimension) d) i =
      ∑ j : Fin (M.ambientDimension i + 1), d ⟨i, j⟩ := by
  classical
  rw [Finsupp.weight_eq_sum, Fintype.sum_sigma]
  change (∑ b : M.FactorIndex,
    ∑ j : Fin (M.ambientDimension b + 1),
      d ⟨b, j⟩ • Hilbert.blockWeight M.factorCount M.ambientDimension ⟨b, j⟩) i = _
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Hilbert.blockWeight,
    Pi.single_apply, mul_ite, mul_one, mul_zero]
  rw [Finset.sum_eq_single i]
  · simp
  · intro b hb hbi
    simp [Ne.symm hbi]
  · simp

theorem degreePiece_iff (P : M.CoordinateRing) (D : M.FactorIndex → ℕ) :
    P ∈ Hilbert.degreePiece K M.factorCount M.ambientDimension D ↔ M.IsHomogeneous P D := by
  change (∀ d, coeff d P ≠ 0 →
    Finsupp.weight (Hilbert.blockWeight M.factorCount M.ambientDimension) d = D) ↔ _
  simp only [← mem_support_iff]
  constructor
  · intro h d hd i
    exact (M.blockWeight_apply d i).symm.trans (congrFun (h d hd) i)
  · intro h d hd
    funext i
    rw [M.blockWeight_apply]
    exact h d hd i


end PhilipponMultiplicity.MultiProjectiveSpace
namespace PhilipponMultiplicity.Hilbert
variable {K : Type*} [Field K] (M : MultiProjectiveSpace K)

theorem prime_of_homogeneous_products (I : Ideal M.CoordinateRing)
    (hI : IsMultihomogeneousIdeal M I) (hne : I ≠ ⊤)
    (hmul : ∀ P Q : M.CoordinateRing, (∃ D, M.IsHomogeneous P D) →
      (∃ E, M.IsHomogeneous Q E) → P * Q ∈ I → P ∈ I ∨ Q ∈ I) : I.IsPrime := by
  classical
  let w : M.Variable → Lex (M.FactorIndex → ℕ) :=
    fun x => toLex (blockWeight M.factorCount M.ambientDimension x)
  letI : DecidableEq (Lex (M.FactorIndex → ℕ)) := LinearOrder.toDecidableEq
  letI := weightedGradedAlgebra K w
  have hIg : I.IsHomogeneous (weightedHomogeneousSubmodule K w) := by
    intro d f hf
    change ((MvPolynomial.decompose' K w f) d : M.CoordinateRing) ∈ I
    rw [MvPolynomial.decompose'_apply]
    have heq : weightedHomogeneousComponent w d f =
        weightedHomogeneousComponent (blockWeight M.factorCount M.ambientDimension) (ofLex d) f := by
      ext e
      simp only [coeff_weightedHomogeneousComponent]
      rfl
    rw [heq]
    exact hI f hf (ofLex d)
  apply hIg.isPrime_of_homogeneous_mem_or_mem hne
  rintro P Q ⟨D, hP⟩ ⟨E, hQ⟩ hPQ
  apply hmul P Q _ _ hPQ
  · exact ⟨ofLex D, (M.degreePiece_iff P (ofLex D)).mp hP⟩
  · exact ⟨ofLex E, (M.degreePiece_iff Q (ofLex E)).mp hQ⟩


end PhilipponMultiplicity.Hilbert
namespace PhilipponMultiplicity

theorem vanishingIdeal_multihomogeneous (K : Type*) [Field K]
    (M : MultiProjectiveSpace K) (S : Set M.Point) :
    IsMultihomogeneousIdeal M (M.vanishingIdeal S) := by
  classical
  let w := Hilbert.blockWeight M.factorCount M.ambientDimension
  letI := MvPolynomial.weightedGradedAlgebra K w
  have hh : (M.vanishingIdeal S).IsHomogeneous (weightedHomogeneousSubmodule K w) := by
    apply Ideal.homogeneous_span
    intro P hP
    obtain ⟨D, hD⟩ := hP.1
    refine ⟨D, ?_⟩
    intro e he
    funext i
    rw [M.blockWeight_apply]
    exact hD e (mem_support_iff.mpr he) i
  intro P hP d
  exact weightedHomogeneousComponent_mem_of_mem K w hh hP d

variable {K : Type*} [Field K]

theorem MultiProjectiveSpace.vanishingIdeal_isPrime_of_isIrreducible
    (M : MultiProjectiveSpace K) (S : Set M.Point)
    (hS : @IsIrreducible _ M.zariskiTopology S) : (M.vanishingIdeal S).IsPrime := by
  classical
  letI : TopologicalSpace M.Point := M.zariskiTopology
  apply Hilbert.prime_of_homogeneous_products M _ (vanishingIdeal_multihomogeneous K M S)
  · intro htop
    obtain ⟨x,hx⟩ := hS.nonempty
    have hz := M.eval_eq_zero_of_mem_vanishingIdeal
      (show (1 : M.CoordinateRing) ∈ M.vanishingIdeal S by rw [htop]; trivial) hx
    exact one_ne_zero (by simpa only [MultiProjectiveSpace.eval,map_one] using hz)
  · rintro P Q ⟨D,hP⟩ ⟨E,hQ⟩ hPQ
    by_contra! hn
    have hnzero (R : M.CoordinateRing) (d : M.FactorIndex → ℕ)
        (hR : M.IsHomogeneous R d) (hRI : R ∉ M.vanishingIdeal S) :
        (S ∩ {x | M.eval R x ≠ 0}).Nonempty := by
      by_contra hz
      apply hRI
      exact Ideal.subset_span ⟨⟨d,hR⟩,fun x hx => by
        by_contra hxR
        exact hz ⟨x,hx,hxR⟩⟩
    obtain ⟨x,hx,hxP,hxQ⟩ := hS.2 _ _ (M.isOpen_basic P D hP)
      (M.isOpen_basic Q E hQ) (hnzero P D hP hn.1) (hnzero Q E hQ hn.2)
    have hz := M.eval_eq_zero_of_mem_vanishingIdeal hPQ hx
    exact (mul_ne_zero hxP hxQ) (by simpa only [MultiProjectiveSpace.eval,map_mul] using hz)


end PhilipponMultiplicity

end
end


section

set_option autoImplicit false
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open scoped BigOperators
open MvPolynomial
noncomputable section

namespace PhilipponMultiplicity.AffineChartDomain
universe u v
variable {K : Type u} [Field K] (M : MultiProjectiveSpace K)

/-- Homogeneous scaling works over an arbitrary coefficient extension. -/
theorem eval₂_block_scale {A : Type v} [CommRing A] (f : K →+* A)
    (P : M.CoordinateRing) (D : M.FactorIndex → ℕ) (hP : M.IsHomogeneous P D)
    (v : M.Variable → A) (a : M.FactorIndex → A) :
    eval₂Hom f (fun j => a j.1 * v j) P =
      (∏ i, a i ^ D i) * eval₂Hom f v P := by
  classical
  simp only [coe_eval₂Hom, eval₂_eq', Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro d hd
  have hscale : (∏ j : M.Variable, a j.1 ^ d j) = ∏ i, a i ^ D i := by
    rw [Fintype.prod_sigma]
    apply Finset.prod_congr rfl
    intro i _
    change (∏ j : Fin (M.ambientDimension i + 1), a i ^ d ⟨i,j⟩) = a i ^ D i
    rw [Finset.prod_pow_eq_pow_sum, hP d hd i]
  simp only [mul_pow, Finset.prod_mul_distrib, hscale]
  ring

theorem normalization_relations_le_ker {A : Type v} [CommRing A]
    (b : ∀ i : M.FactorIndex, Fin (M.ambientDimension i + 1))
    (f : M.CoordinateRing →+* A) (hf : ∀ i, f (X (⟨i,b i⟩ : M.Variable)) = 1) :
    Ideal.span (Set.range (fun i : M.FactorIndex =>
      (X (⟨i,b i⟩ : M.Variable) : M.CoordinateRing) - 1)) ≤ RingHom.ker f := by
  apply Ideal.span_le.mpr
  rintro P ⟨i,rfl⟩
  change f (X (⟨i,b i⟩ : M.Variable) - 1) = 0
  rw [map_sub, map_one, hf i, sub_self]

end PhilipponMultiplicity.AffineChartDomain
end
end


section

set_option autoImplicit false
set_option maxHeartbeats 500000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open scoped BigOperators
open MvPolynomial
noncomputable section
namespace PhilipponMultiplicity.AffineChartHomogeneous
universe u
variable {K : Type u} [Field K] (M : MultiProjectiveSpace K)

def chartIdeal (W : Set M.Point)
    (b : ∀ i : M.FactorIndex, Fin (M.ambientDimension i + 1)) : Ideal M.CoordinateRing :=
  M.vanishingIdeal W ⊔ Ideal.span (Set.range (fun i : M.FactorIndex =>
    (X (⟨i,b i⟩ : M.Variable) : M.CoordinateRing) - 1))

theorem homogeneous_mem_chart_iff (W : Set M.Point)
    (hirr : @IsIrreducible _ M.zariskiTopology W)
    (b : ∀ i : M.FactorIndex, Fin (M.ambientDimension i + 1))
    [hnon : Nontrivial (M.CoordinateRing ⧸ chartIdeal M W b)]
    {P : M.CoordinateRing} {D : M.FactorIndex → ℕ} (hP : M.IsHomogeneous P D) :
    P ∈ chartIdeal M W b ↔ P ∈ M.vanishingIdeal W := by
  classical
  let I := M.vanishingIdeal W
  let J := I ⊔ Ideal.span (Set.range (fun i : M.FactorIndex =>
    (X (⟨i,b i⟩ : M.Variable) : M.CoordinateRing) - 1))
  let S := M.CoordinateRing ⧸ J
  letI : Nontrivial S := hnon
  let q : M.CoordinateRing →+* S := Ideal.Quotient.mk J
  have hq (i) : q (X (⟨i,b i⟩ : M.Variable)) = 1 := by
    have hz : q ((X (⟨i,b i⟩ : M.Variable) : M.CoordinateRing) - 1) = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.mpr
        ((le_sup_right : Ideal.span _ ≤ J) (Ideal.subset_span ⟨i,rfl⟩))
    simpa only [map_sub, map_one, sub_eq_zero] using hz
  letI : I.IsPrime := M.vanishingIdeal_isPrime_of_isIrreducible W hirr
  let R := M.CoordinateRing ⧸ I
  letI : IsDomain R := inferInstance
  let F := FractionRing R
  letI : Field F := inferInstance
  let f : M.CoordinateRing →+* F := (algebraMap R F).comp (Ideal.Quotient.mk I)
  have hf (P : M.CoordinateRing) : f P = 0 ↔ P ∈ I := by
    change algebraMap R F (Ideal.Quotient.mk I P) = 0 ↔ P ∈ I
    rw [map_eq_zero_iff _ (IsFractionRing.injective R F), Ideal.Quotient.eq_zero_iff_mem]
  have hpivot (i) : f (X (⟨i,b i⟩ : M.Variable)) ≠ 0 := by
    intro hz
    have hzq : q (X (⟨i,b i⟩ : M.Variable)) = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.mpr
        ((le_sup_left : I ≤ J) ((hf _).mp hz))
    exact one_ne_zero ((hq i).symm.trans hzq)
  let a (i : M.FactorIndex) : F := (f (X (⟨i,b i⟩ : M.Variable)))⁻¹
  let φ : M.CoordinateRing →+* F := eval₂Hom (f.comp C) (fun j => a j.1 * f (X j))
  have hself : eval₂Hom (f.comp C) (fun j => f (X j)) = f := by
    apply MvPolynomial.ringHom_ext
    · intro c
      simp
    · intro j
      simp
  have hφhom (P : M.CoordinateRing) (D : M.FactorIndex → ℕ)
      (hP : M.IsHomogeneous P D) : φ P = (∏ i, a i ^ D i) * f P := by
    have h := AffineChartDomain.eval₂_block_scale M (f.comp C) P D hP (fun j => f (X j)) a
    rw [hself] at h
    exact h
  have hφpivot (i) : φ (X (⟨i,b i⟩ : M.Variable)) = 1 := by
    dsimp only [φ]
    rw [eval₂Hom_X']
    change (f (X (⟨i,b i⟩ : M.Variable)))⁻¹ * f (X (⟨i,b i⟩ : M.Variable)) = 1
    exact inv_mul_cancel₀ (hpivot i)
  have hI : I ≤ RingHom.ker φ := by
    apply Ideal.span_le.mpr
    rintro P ⟨⟨D,hP⟩, hz⟩
    change φ P = 0
    rw [hφhom P D hP, (hf P).mpr (Ideal.subset_span ⟨⟨D,hP⟩,hz⟩), mul_zero]
  have hJ : J ≤ RingHom.ker φ := by
    exact sup_le hI (AffineChartDomain.normalization_relations_le_ker M b φ hφpivot)
  constructor
  · intro hPJ
    have hz : φ P = 0 := hJ hPJ
    rw [hφhom P D hP] at hz
    have ha : (∏ i, a i ^ D i) ≠ 0 := by
      apply Finset.prod_ne_zero_iff.mpr
      intro i _
      exact pow_ne_zero _ (inv_ne_zero (hpivot i))
    exact (hf P).mp ((mul_eq_zero.mp hz).resolve_left ha)
  · intro hP
    exact (le_sup_left : M.vanishingIdeal W ≤ chartIdeal M W b) hP

end PhilipponMultiplicity.AffineChartHomogeneous
end
end


section

set_option autoImplicit false
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace PhilipponMultiplicity.GenericBoundaryAlgebra
open MvPolynomial

section Localization
attribute [local instance] MvPolynomial.algebraMvPolynomial

/-- A prime polynomial ideal stays prime after coefficient localization,
provided the localized ideal is proper, and contracts to the original ideal. -/
theorem prime_and_contraction {R σ : Type*} [CommRing R] [IsDomain R]
    (I : Ideal (MvPolynomial σ R)) (hI : I.IsPrime)
    (hne : I.map (map (algebraMap R (FractionRing R))) ≠ ⊤) :
    (I.map (map (algebraMap R (FractionRing R)))).IsPrime ∧
    (I.map (map (algebraMap R (FractionRing R)))).comap
      (map (algebraMap R (FractionRing R))) = I := by
  let S := (nonZeroDivisors R).map (C (σ := σ))
  let A := MvPolynomial σ (FractionRing R)
  change I.map (algebraMap (MvPolynomial σ R) A) ≠ ⊤ at hne
  have hdis := (IsLocalization.map_algebraMap_ne_top_iff_disjoint S A I).mp hne
  exact ⟨IsLocalization.isPrime_of_isPrime_disjoint S A I hI hdis,
    IsLocalization.under_map_of_isPrime_disjoint S A hI hdis⟩

end Localization

/-- A prime ideal with finite-dimensional quotient over a field is maximal. -/
theorem maximal_of_finite_quotient {K σ : Type*} [Field K]
    (I : Ideal (MvPolynomial σ K)) [I.IsPrime]
    [Module.Finite K (MvPolynomial σ K ⧸ I)] : I.IsMaximal := by
  have hf : IsField (MvPolynomial σ K ⧸ I) :=
    isField_of_isIntegral_of_isField' (R := K) (Field.toIsField K)
  exact Ideal.Quotient.maximal_of_isField I hf

end PhilipponMultiplicity.GenericBoundaryAlgebra

end
end


section

set_option autoImplicit false
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open scoped BigOperators
noncomputable section
namespace PhilipponMultiplicity.GenericBoundaryCharts
open MvPolynomial GenericMixedSections AffineChartHomogeneous
variable {K : Type*} [Field K] (M : MultiProjectiveSpace K)

/-- A proper closed boundary admits a homogeneous equation that does not
vanish identically on the containing locus. -/
theorem exists_boundary_equation (W B : Set M.Point)
    (hB : @IsClosed _ M.zariskiTopology B) (hWB : (W \ B).Nonempty) :
    ∃ P : M.CoordinateRing, ∃ D : M.FactorIndex → ℕ,
      M.IsHomogeneous P D ∧ P ∈ M.vanishingIdeal B ∧ P ∉ M.vanishingIdeal W := by
  let := M.zariskiTopology
  obtain ⟨x,hxW,hxB⟩ := hWB
  obtain ⟨U,⟨P,D,hP,rfl⟩,hxP,hPB⟩ :=
    M.isTopologicalBasis_basic.exists_subset_of_mem_open hxB hB.isOpen_compl
  refine ⟨P,D,hP,Ideal.subset_span ⟨⟨D,hP⟩,?_⟩,?_⟩
  · intro y hy
    by_contra hyP
    exact hPB hyP hy
  · intro hPW
    exact hxP (M.eval_eq_zero_of_mem_vanishingIdeal hPW hxW)

theorem vanishingIdeal_antitone {W B : Set M.Point} (hBW : B ⊆ W) :
    M.vanishingIdeal W ≤ M.vanishingIdeal B := by
  apply Ideal.span_le.mpr
  rintro P ⟨hhom,hW⟩
  exact Ideal.subset_span ⟨hhom,fun x hx => hW x (hBW hx)⟩

variable (l : List M.FactorIndex)

/-- Set every cutting coefficient to zero while retaining ambient variables. -/
def zeroCoefficients : UniversalRing M l →+* M.CoordinateRing :=
  map (eval (fun _ => (0 : K)))

@[simp] theorem zeroCoefficients_fixed (P : M.CoordinateRing) :
    zeroCoefficients M l (map C P) = P := by
  induction P using MvPolynomial.induction_on with
  | C a => simp [zeroCoefficients]
  | add p q hp hq => simp [hp,hq]
  | mul_X p i hp =>
    simpa only [zeroCoefficients, map_mul, map_X] using
      congrArg (fun Q : M.CoordinateRing => Q * X i) hp

@[simp] theorem zeroCoefficients_row (j : Fin l.length) :
    zeroCoefficients M l (universalRow M l j) = 0 := by
  simp [zeroCoefficients, universalRow]

variable (W : Set M.Point)
    (b : ∀ i : M.FactorIndex, Fin (M.ambientDimension i + 1))

theorem chart_le_comap : chartIdeal M W b ≤
    (normalizedIdeal M l W b).comap (map C) := by
  apply sup_le
  · intro P hP
    exact Ideal.mem_sup_left (Ideal.mem_sup_left (Ideal.mem_map_of_mem _ hP))
  · apply Ideal.span_le.mpr
    rintro P ⟨i,rfl⟩
    change map C (X (⟨i,b i⟩ : M.Variable) - 1) ∈ normalizedIdeal M l W b
    rw [map_sub, map_X, map_one]
    exact Ideal.mem_sup_right (Ideal.subset_span (Set.mem_range_self i))

def chartToUniversal : M.CoordinateRing ⧸ chartIdeal M W b →+*
    UniversalRing M l ⧸ normalizedIdeal M l W b :=
  Ideal.quotientMap _ (map C) (chart_le_comap M l W b)

theorem normalized_le_zero_comap : normalizedIdeal M l W b ≤
    (chartIdeal M W b).comap (zeroCoefficients M l) := by
  apply sup_le
  · apply sup_le
    · apply Ideal.map_le_iff_le_comap.mpr
      intro P hP
      change zeroCoefficients M l (map C P) ∈ chartIdeal M W b
      rw [zeroCoefficients_fixed]
      exact Ideal.mem_sup_left hP
    · refine iSup_le fun j => Ideal.span_le.mpr ?_
      rintro P rfl
      change zeroCoefficients M l (universalRow M l j) ∈ chartIdeal M W b
      rw [zeroCoefficients_row]
      exact Ideal.zero_mem _
  · apply Ideal.span_le.mpr
    rintro P ⟨i,rfl⟩
    change zeroCoefficients M l (X (⟨i,b i⟩ : M.Variable) - 1) ∈ chartIdeal M W b
    simp only [zeroCoefficients, map_sub, map_X, map_one]
    exact Ideal.mem_sup_right (Ideal.subset_span (Set.mem_range_self i))

/-- A homogeneous equation nonzero on the irreducible locus remains nonzero
in every nonempty universal normalized chart. -/
theorem fixed_not_mem_normalized
    (hirr : @IsIrreducible _ M.zariskiTopology W)
    [Nontrivial (UniversalRing M l ⧸ normalizedIdeal M l W b)]
    {P : M.CoordinateRing} {D : M.FactorIndex → ℕ}
    (hP : M.IsHomogeneous P D) (hPW : P ∉ M.vanishingIdeal W) :
    map C P ∉ normalizedIdeal M l W b := by
  let := (chartToUniversal M l W b).domain_nontrivial
  intro hmem
  have hchart := normalized_le_zero_comap M l W b hmem
  rw [Ideal.mem_comap, zeroCoefficients_fixed] at hchart
  exact hPW ((homogeneous_mem_chart_iff M W hirr b hP).mp hchart)

end PhilipponMultiplicity.GenericBoundaryCharts

end
end


section

set_option autoImplicit false
set_option maxHeartbeats 300000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open scoped BigOperators
noncomputable section
namespace PhilipponMultiplicity.GenericIncidence
open GenericMixedSections GenericBoundaryCharts GenericBoundaryAlgebra MvPolynomial

/-- The generic normalized section avoids every proper closed boundary.
The only input is the already established incidence domain and dimension. -/
theorem generic_boundary_eq_top {K : Type*} [Field K]
    (M : MultiProjectiveSpace K) (W B : Set M.Point) (l : List M.FactorIndex)
    (b : ∀ i : M.FactorIndex, Fin (M.ambientDimension i + 1))
    (hirr : @IsIrreducible _ M.zariskiTopology W)
    (hB : @IsClosed _ M.zariskiTopology B) (hBW : B ⊆ W)
    (hnonempty : (W \ B).Nonempty)
    (h : Nontrivial (MixedFamily.CoordinateRing M W l b 1) →
      IsDomain (MixedFamily.CoordinateRing M W l b 1) ∧
      ringKrullDim (MixedFamily.CoordinateRing M W l b 1) =
        Nat.card (Fin l.length × M.Variable)) :
    (normalizedIdeal M l B b).map (genericMap M l) = ⊤ := by
  classical
  let I := normalizedIdeal M l W b
  let J := I.map (genericMap M l)
  let JB := (normalizedIdeal M l B b).map (genericMap M l)
  have hle : I ≤ normalizedIdeal M l B b := by
    apply sup_le_sup_right
    apply sup_le_sup_right
    exact Ideal.map_mono (vanishingIdeal_antitone M hBW)
  have hleJ : J ≤ JB := Ideal.map_mono hle
  change JB = ⊤
  by_contra hJB
  have hJ : J ≠ ⊤ := ne_top_of_le_ne_top hJB hleJ
  let V := MvPolynomial M.Variable (FractionRing (CoeffRing M l)) ⧸ J
  let : Nontrivial V := Ideal.Quotient.nontrivial_iff.mpr hJ
  let f : UniversalRing M l ⧸ I →+* V :=
    Ideal.quotientMap J (genericMap M l) Ideal.le_comap_map
  let hU := f.domain_nontrivial
  have hC := (quotientFromTotal M l W b).domain_nontrivial
  let := (h hC).1
  let : IsDomain (UniversalRing M l ⧸ I) :=
    (quotient_leftInverse M l W b).injective.isDomain _
  have hI : I.IsPrime := (Ideal.Quotient.isDomain_iff_prime I).mp inferInstance
  obtain ⟨hprime,hcontract⟩ := prime_and_contraction I hI hJ
  let : J.IsPrime := hprime
  let : Module.Finite (FractionRing (CoeffRing M l)) V :=
    generic_normalized_finite M W l b h
  have hmax : J.IsMaximal := maximal_of_finite_quotient J
  have heq : J = JB := hmax.eq_of_le hJB hleJ
  obtain ⟨P,D,hP,hPB,hPW⟩ := exists_boundary_equation M W B hB hnonempty
  have hpnon : map C P ∉ I := fixed_not_mem_normalized M l W b hirr hP hPW
  apply hpnon
  rw [← hcontract]
  change genericMap M l (map C P) ∈ J
  rw [heq]
  apply Ideal.mem_map_of_mem
  exact Ideal.mem_sup_left (Ideal.mem_sup_left (Ideal.mem_map_of_mem _ hPB))

end PhilipponMultiplicity.GenericIncidence

end
end


section

set_option autoImplicit false
set_option maxHeartbeats 300000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open scoped BigOperators Topology
noncomputable section
namespace PhilipponMultiplicity
open SectionThree SectionThreeSupport
namespace GenericIncidence

/-- Exact boundary-avoidance statement, conditional only on the already
Proved incidence theorem and with no Open geometric hypothesis. -/
theorem boundary_of_incidence
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
          Nat.card (Fin l.length × M.Variable)) :
    ∀ (M : MultiProjectiveSpace K) (W : Set M.Point),
      @IsClosed _ M.zariskiTopology W → @IsIrreducible _ M.zariskiTopology W →
      ∀ (α : M.FactorIndex → ℕ), (∀ i, α i ≤ M.ambientDimension i) →
      (∑ i, α i = locusDimension M W) →
      ∀ B : Set M.Point, @IsClosed _ M.zariskiTopology B → B ⊆ W →
      (W \ B).Nonempty →
      ∀ l : List M.FactorIndex, (∀ i, l.count i = α i) →
        ∀ b : ∀ i : M.FactorIndex, Fin (M.ambientDimension i + 1),
          (GenericMixedSections.normalizedIdeal M l B b).map
            (GenericMixedSections.genericMap M l) = ⊤ := by
  intro M W hW hirr α hα hdim B hB hBW hnonempty l hl b
  exact generic_boundary_eq_top M W B l b hirr hB hBW hnonempty
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
          (GenericMixedSections.normalizedIdeal M l B b).map
            (GenericMixedSections.genericMap M l) = ⊤ := by
  exact GenericIncidence.boundary_of_incidence K hK
    (mixed_incidence_domain_and_dimension K hK)
