-- Prove2me | solution 1 for PhilipponMultiplicity.generic_mixed_sections_finite_reduced
-- status  : ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-10-08T22:18:52.167665+00:00
-- url     : https://prove2.me/submissions/5a631411-a2c9-4faa-8e9c-d11389746930

import Theorems.Thm_PhilipponMultiplicity_generic_mixed_sections_finite
import Theorems.Thm_PhilipponMultiplicity_mixed_incidence_domain_and_dimension
import Definitions.Def_PhilipponMultiplicity_GenericMixedSections
import Definitions.Def_PhilipponMultiplicity_GeometricSupport
import Definitions.Def_PhilipponMultiplicity_UniversalMixedSlices


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
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open scoped BigOperators
open MvPolynomial
noncomputable section

namespace PhilipponMultiplicity.GenericIncidence
open GenericMixedSections
attribute [local instance] MvPolynomial.algebraMvPolynomial

/-- Extending coefficients from a domain to its fraction field preserves
reducedness of a polynomial quotient. The result includes the zero ring. -/
theorem generic_quotient_isReduced
    {R σ : Type*} [CommRing R] [IsDomain R]
    (I : Ideal (MvPolynomial σ R)) [IsReduced (MvPolynomial σ R ⧸ I)] :
    IsReduced (MvPolynomial σ (FractionRing R) ⧸
      I.map (map (algebraMap R (FractionRing R)))) := by
  let S := (nonZeroDivisors R).map (C (σ := σ))
  have hI : I.IsRadical := (Ideal.isRadical_iff_quotient_reduced I).mpr inferInstance
  apply (Ideal.isRadical_iff_quotient_reduced _).mp
  apply Ideal.radical_eq_iff.mp
  change (I.map (algebraMap (MvPolynomial σ R)
    (MvPolynomial σ (FractionRing R)))).radical = _
  rw [← IsLocalization.map_radical S, hI.radical]
  rfl

/-- The generic normalized chart is reduced once the already established
incidence ring has its domain property. No transversality input is needed. -/
theorem generic_normalized_isReduced
    {K : Type*} [Field K] (M : MultiProjectiveSpace K)
    (W : Set M.Point) (l : List M.FactorIndex)
    (b : ∀ i : M.FactorIndex, Fin (M.ambientDimension i + 1))
    (h : Nontrivial (MixedFamily.CoordinateRing M W l b 1) →
      IsDomain (MixedFamily.CoordinateRing M W l b 1)) :
    IsReduced (MvPolynomial M.Variable (FractionRing (CoeffRing M l)) ⧸
      (normalizedIdeal M l W b).map (genericMap M l)) := by
  let := normalized_isReduced_of_incidence M l W b h
  exact generic_quotient_isReduced (normalizedIdeal M l W b)

end PhilipponMultiplicity.GenericIncidence
end
end


section

set_option autoImplicit false
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open scoped BigOperators Topology
noncomputable section
namespace PhilipponMultiplicity
open SectionThree SectionThreeSupport
namespace GenericIncidence

/-- The remaining generic geometry supplies finiteness and boundary avoidance;
reducedness follows from the existing incidence theorem and coefficient localization. -/
theorem finite_reduced_of_finite
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
    (hgeometry : ∀ (M : MultiProjectiveSpace K) (W : Set M.Point),
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
          IsReduced (MvPolynomial M.Variable (FractionRing (GenericMixedSections.CoeffRing M l)) ⧸
              (GenericMixedSections.normalizedIdeal M l W b).map
                (GenericMixedSections.genericMap M l)) ∧
          (GenericMixedSections.normalizedIdeal M l B b).map
            (GenericMixedSections.genericMap M l) = ⊤ := by
  intro M W hW hirr α hα hdim B hB hBW hnonempty l hl b
  obtain ⟨hfinite,hboundary⟩ :=
    hgeometry M W hW hirr α hα hdim B hB hBW hnonempty l hl b
  refine ⟨hfinite, ?_, hboundary⟩
  exact generic_normalized_isReduced M W l b
    (fun hn => (hincidence M W hW hirr α hα hdim l hl b 1 hn).1)

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
          IsReduced (MvPolynomial M.Variable (FractionRing (GenericMixedSections.CoeffRing M l)) ⧸
              (GenericMixedSections.normalizedIdeal M l W b).map
                (GenericMixedSections.genericMap M l)) ∧
          (GenericMixedSections.normalizedIdeal M l B b).map
            (GenericMixedSections.genericMap M l) = ⊤ := by
  exact GenericIncidence.finite_reduced_of_finite K hK
    (mixed_incidence_domain_and_dimension K hK)
    (generic_mixed_sections_finite K hK)
