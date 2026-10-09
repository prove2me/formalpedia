-- Prove2me | solution 1 for PhilipponMultiplicity.exists_principal_open_reduced_point_mixed_zero_locus
-- status  : ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-10-08T20:30:06.64251+00:00
-- url     : https://prove2.me/submissions/1a8edbe1-b39c-462a-8819-942ebfeddb13

import Theorems.Thm_PhilipponMultiplicity_exists_principal_open_reduced_normalized_mixed_sections
import Definitions.Def_PhilipponMultiplicity_GeometricSupport
import Definitions.Def_PhilipponMultiplicity_Geometry
import Definitions.Def_PhilipponMultiplicity_MixedFlagParameters
import Mathlib


section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open scoped BigOperators
open MvPolynomial
noncomputable section
namespace PhilipponMultiplicity.AffineChartDomain
universe u v
variable {K : Type u} [Field K] (M : MultiProjectiveSpace K)
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


end PhilipponMultiplicity.AffineChartDomain
namespace PhilipponMultiplicity.MixedFlag
variable {K : Type*} [Field K] (M : MultiProjectiveSpace K)
theorem rowForm_homogeneous (b : M.FactorIndex) (a : M.Variable → K) :
    M.IsHomogeneous (rowForm M b a) (Pi.single b 1) := by
  classical
  intro m hm i
  change m ∈ (∑ t : Fin (M.ambientDimension b + 1),
    a ⟨b,t⟩ • (MvPolynomial.X ⟨b,t⟩ : M.CoordinateRing)).support at hm
  have hs := MvPolynomial.support_sum (s := Finset.univ)
    (f := fun t : Fin (M.ambientDimension b + 1) =>
      a ⟨b,t⟩ • (MvPolynomial.X ⟨b,t⟩ : M.CoordinateRing)) hm
  obtain ⟨t, _, ht⟩ := Finset.mem_biUnion.mp hs
  have hmX : m ∈ (MvPolynomial.X (⟨b,t⟩ : M.Variable) : M.CoordinateRing).support :=
    MvPolynomial.support_smul ht
  simp only [MvPolynomial.support_X, Finset.mem_singleton] at hmX
  subst m
  by_cases hi : i = b
  · subst i
    simp [Finsupp.single_apply, Sigma.mk.inj_iff, Pi.single_apply]
  · have hn (k : Fin (M.ambientDimension i + 1)) :
        (⟨b,t⟩ : M.Variable) ≠ ⟨i,k⟩ := by
      intro h
      exact hi (congrArg Sigma.fst h).symm
    simp [Finsupp.single_apply, Pi.single_apply, hi, hn]

theorem polynomial_homogeneous (l : List M.FactorIndex)
    (c : Fin l.length → M.Variable → K) (j : Fin l.length) :
    M.IsHomogeneous (polynomial M l c j) (Pi.single l[j] 1) :=
  rowForm_homogeneous M l[j] (c j)


end PhilipponMultiplicity.MixedFlag
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

namespace PhilipponMultiplicity.NormalizedChartRadical

variable {K : Type*} [Field K] (M : MultiProjectiveSpace K)

/-- Reducedness of the normalized chart supplies a radical ideal between the
original homogeneous ideal and any kernel in which the chosen pivots are units. -/
theorem exists_radical_between
    (I : Ideal M.CoordinateRing) (hI : M.IsHomogeneousIdeal I)
    (b : ∀ i : M.FactorIndex, Fin (M.ambientDimension i + 1))
    (hrad : (I ⊔ Ideal.span (Set.range (fun i : M.FactorIndex =>
      (X (⟨i,b i⟩ : M.Variable) : M.CoordinateRing) - 1))).IsRadical)
    {S : Type*} [CommRing S] (f : M.CoordinateRing →+* S)
    (hf : I ≤ RingHom.ker f)
    (hu : ∀ i, IsUnit (f (X (⟨i,b i⟩ : M.Variable)))) :
    ∃ L : Ideal M.CoordinateRing, L.IsRadical ∧ I ≤ L ∧ L ≤ RingHom.ker f := by
  classical
  let J := I ⊔ Ideal.span (Set.range (fun i : M.FactorIndex =>
    (X (⟨i,b i⟩ : M.Variable) : M.CoordinateRing) - 1))
  let C' := M.CoordinateRing ⧸ J
  let q : M.CoordinateRing →+* C' := Ideal.Quotient.mk J
  let : IsReduced C' := (Ideal.isRadical_iff_quotient_reduced J).mp hrad
  let T := MvPolynomial M.FactorIndex C'
  let ψ : M.CoordinateRing →+* T :=
    eval₂Hom (MvPolynomial.C.comp (q.comp MvPolynomial.C))
      (fun j => X j.1 * MvPolynomial.C (q (X j)))
  have hbase : eval₂Hom ((MvPolynomial.C : C' →+* T).comp (q.comp MvPolynomial.C))
      (fun j : M.Variable => MvPolynomial.C (q (X j))) = MvPolynomial.C.comp q := by
    apply MvPolynomial.ringHom_ext <;> intros <;> simp
  have hIψ : I ≤ RingHom.ker ψ := by
    rw [hI]
    apply Ideal.span_le.mpr
    rintro P ⟨hP, D, hD⟩
    change ψ P = 0
    have hs := AffineChartDomain.eval₂_block_scale M
      (MvPolynomial.C.comp (q.comp MvPolynomial.C)) P D hD
      (fun j => MvPolynomial.C (q (X j))) (fun i => X i)
    rw [hbase] at hs
    change ψ P = (∏ i, (X i : T) ^ D i) * MvPolynomial.C (q P) at hs
    rw [hs]
    have hqP : q P = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr
      ((le_sup_left : I ≤ J) hP)
    simp [hqP]
  choose u hu using hu
  let η : M.CoordinateRing →+* S := eval₂Hom (f.comp MvPolynomial.C)
    (fun j => (↑((u j.1)⁻¹) : S) * f (X j))
  have hself : eval₂Hom (f.comp MvPolynomial.C)
      (fun j : M.Variable => f (X j)) = f := by
    apply MvPolynomial.ringHom_ext <;> intros <;> simp
  have hIη : I ≤ RingHom.ker η := by
    rw [hI]
    apply Ideal.span_le.mpr
    rintro P ⟨hP, D, hD⟩
    change η P = 0
    have hs := AffineChartDomain.eval₂_block_scale M (f.comp MvPolynomial.C)
      P D hD (fun j => f (X j)) (fun i => (↑((u i)⁻¹) : S))
    rw [hself] at hs
    change η P = _ at hs
    rw [hs, show f P = 0 from hf hP, mul_zero]
  have hηpivot (i) : η (X (⟨i,b i⟩ : M.Variable)) = 1 := by
    dsimp only [η]
    rw [eval₂Hom_X']
    rw [← hu i]
    exact Units.inv_mul (u i)
  have hJη : J ≤ RingHom.ker η := by
    apply sup_le hIη
    apply Ideal.span_le.mpr
    rintro _ ⟨i, rfl⟩
    change η (X (⟨i,b i⟩ : M.Variable) - 1) = 0
    rw [map_sub, map_one, hηpivot, sub_self]
  let g : C' →+* S := Ideal.Quotient.lift J η hJη
  let φ : T →+* S := eval₂Hom g (fun i => (u i : S))
  have hg (P : M.CoordinateRing) : g (q P) = η P :=
    Ideal.Quotient.lift_mk J η hJη
  have hφC (x : C') : φ (MvPolynomial.C x) = g x := eval₂Hom_C _ _ _
  have hφX (i : M.FactorIndex) : φ (X i) = (u i : S) := eval₂Hom_X' _ _ _
  have hcomp : φ.comp ψ = f := by
    apply MvPolynomial.ringHom_ext
    · intro k
      change φ (ψ (MvPolynomial.C k)) = f (MvPolynomial.C k)
      rw [show ψ (MvPolynomial.C k) = MvPolynomial.C (q (MvPolynomial.C k))
        from eval₂Hom_C _ _ _, hφC, hg]
      exact eval₂Hom_C _ _ _
    · intro j
      change φ (ψ (X j)) = f (X j)
      rw [show ψ (X j) = X j.1 * MvPolynomial.C (q (X j))
        from eval₂Hom_X' _ _ _, map_mul, hφX, hφC, hg]
      rw [show η (X j) = (↑((u j.1)⁻¹) : S) * f (X j) from eval₂Hom_X' _ _ _]
      simp [← mul_assoc]
  refine ⟨RingHom.ker ψ, ?_, hIψ, ?_⟩
  · exact (Ideal.isRadical_bot : (⊥ : Ideal T).IsRadical).comap ψ
  · intro P hP
    change f P = 0
    rw [← hcomp]
    change φ (ψ P) = 0
    rw [show ψ P = 0 from hP, map_zero]

/-- A localization that inverts all chosen pivots preserves radicality
from the normalized chart. -/
theorem localization_of_chart
    (I : Ideal M.CoordinateRing) (hI : M.IsHomogeneousIdeal I)
    (b : ∀ i : M.FactorIndex, Fin (M.ambientDimension i + 1))
    (hrad : (I ⊔ Ideal.span (Set.range (fun i : M.FactorIndex =>
      (X (⟨i,b i⟩ : M.Variable) : M.CoordinateRing) - 1))).IsRadical)
    (s : Submonoid M.CoordinateRing) (S : Type*) [CommRing S]
    [Algebra M.CoordinateRing S] [IsLocalization s S]
    (hpivot : ∀ i, IsUnit (algebraMap M.CoordinateRing S (X (⟨i,b i⟩ : M.Variable)))) :
    (I.map (algebraMap M.CoordinateRing S)).IsRadical := by
  let a : M.CoordinateRing →+* S := algebraMap _ _
  let J := I.map a
  let f : M.CoordinateRing →+* (S ⧸ J) := (Ideal.Quotient.mk J).comp a
  have hf : I ≤ RingHom.ker f := by
    intro P hP
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_map_of_mem a hP)
  have hu (i) : IsUnit (f (X (⟨i,b i⟩ : M.Variable))) :=
    (hpivot i).map (Ideal.Quotient.mk J)
  obtain ⟨L, hL, hIL, hLf⟩ := exists_radical_between M I hI b hrad f hf hu
  have heq : J = L.map a := by
    apply le_antisymm (Ideal.map_mono hIL)
    apply Ideal.map_le_iff_le_comap.mpr
    intro P hP
    change a P ∈ J
    exact Ideal.Quotient.eq_zero_iff_mem.mp (hLf hP)
  change J.IsRadical
  rw [heq]
  apply Ideal.radical_eq_iff.mp
  rw [← IsLocalization.map_radical s S L, hL.radical]

/-- At a representative where the chosen pivots do not vanish, radicality of
the normalized chart implies radicality of the original localized ideal. -/
theorem point_local_of_chart
    (I : Ideal M.CoordinateRing) (hI : M.IsHomogeneousIdeal I)
    (b : ∀ i : M.FactorIndex, Fin (M.ambientDimension i + 1))
    (hrad : (I ⊔ Ideal.span (Set.range (fun i : M.FactorIndex =>
      (X (⟨i,b i⟩ : M.Variable) : M.CoordinateRing) - 1))).IsRadical)
    (v : M.Variable → K) (hb : ∀ i, v ⟨i,b i⟩ ≠ 0) :
    (I.map (algebraMap M.CoordinateRing
      (Localization.AtPrime (vanishingIdeal K {v})))).IsRadical := by
  apply localization_of_chart M I hI b hrad (vanishingIdeal K {v}).primeCompl
  intro i
  exact IsLocalization.map_units (Localization.AtPrime (vanishingIdeal K {v}))
    (⟨X (⟨i,b i⟩ : M.Variable), by simpa [vanishingIdeal] using hb i⟩ :
      (vanishingIdeal K {v}).primeCompl)

end PhilipponMultiplicity.NormalizedChartRadical
end
end


section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open scoped BigOperators Topology
noncomputable section

namespace PhilipponMultiplicity.NormalizedChartRadical

variable {K : Type*} [Field K] (M : MultiProjectiveSpace K)

/-- The actual mixed-flag ideal is generated by multihomogeneous polynomials. -/
theorem mixed_ideal_homogeneous (W : Set M.Point) (l : List M.FactorIndex)
    (c : Fin l.length → M.Variable → K) (k : ℕ) :
    M.IsHomogeneousIdeal (MixedFlag.ideal M (M.vanishingIdeal W) l c k) := by
  classical
  let I := MixedFlag.ideal M (M.vanishingIdeal W) l c k
  change I = Ideal.span {P | P ∈ I ∧ ∃ D, M.IsHomogeneous P D}
  apply le_antisymm
  · change M.vanishingIdeal W ⊔ _ ≤ _
    apply sup_le
    · apply Ideal.span_le.mpr
      intro P hP
      exact Ideal.subset_span
        ⟨(le_sup_left : M.vanishingIdeal W ≤ I) (Ideal.subset_span hP), hP.1⟩
    · apply iSup_le
      intro j
      apply iSup_le
      intro hj
      apply Ideal.span_le.mpr
      rintro P (rfl : P = MixedFlag.polynomial M l c j)
      apply Ideal.subset_span
      refine ⟨?_, _, MixedFlag.polynomial_homogeneous M l c j⟩
      have hle : Ideal.span {MixedFlag.polynomial M l c j} ≤ I :=
        le_sup_of_le_right (le_iSup_of_le j (le_iSup_of_le hj le_rfl))
      exact hle (Ideal.subset_span (Set.mem_singleton _))
  · exact Ideal.span_le.mpr (fun _ hP => hP.1)

open SectionThree SectionThreeSupport

/-- Generic radicality in normalized charts suffices for the original
representative-local radicality statement, without changing its ideal. -/
theorem reduced_point_sections_of_normalized
    (K : Type*) [NontriviallyNormedField K] (hK : IsPhilipponBaseField K)
    (hgeometry : ∀ (M : MultiProjectiveSpace K) (W : Set M.Point),
      @IsClosed _ M.zariskiTopology W → @IsIrreducible _ M.zariskiTopology W →
      ∀ (α : M.FactorIndex → ℕ), (∀ i, α i ≤ M.ambientDimension i) →
      (∑ i, α i = locusDimension M W) →
      ∀ B : Set M.Point, @IsClosed _ M.zariskiTopology B → B ⊆ W →
      (W \ B).Nonempty →
      ∀ l : List M.FactorIndex, (∀ i, l.count i = α i) →
        ∃ F : MvPolynomial (Fin l.length × M.Variable) K, F ≠ 0 ∧
          ∀ c : Fin l.length → M.Variable → K,
            MvPolynomial.eval (Function.uncurry c) F ≠ 0 →
            ({x : M.Point | x ∈ W ∧
              ∀ j : Fin l.length, M.eval (MixedFlag.polynomial M l c j) x = 0}).Finite ∧
            Disjoint {x : M.Point | x ∈ W ∧
              ∀ j : Fin l.length, M.eval (MixedFlag.polynomial M l c j) x = 0} B ∧
            (∀ b : ∀ i : M.FactorIndex, Fin (M.ambientDimension i + 1),
              (MixedFlag.ideal M (M.vanishingIdeal W) l c l.length ⊔
                Ideal.span (Set.range (fun i : M.FactorIndex =>
                  (MvPolynomial.X (⟨i,b i⟩ : M.Variable) : M.CoordinateRing) - 1))).IsRadical)) :
    ∀ (M : MultiProjectiveSpace K) (W : Set M.Point),
      @IsClosed _ M.zariskiTopology W → @IsIrreducible _ M.zariskiTopology W →
      ∀ (α : M.FactorIndex → ℕ), (∀ i, α i ≤ M.ambientDimension i) →
      (∑ i, α i = locusDimension M W) →
      ∀ B : Set M.Point, @IsClosed _ M.zariskiTopology B → B ⊆ W →
      (W \ B).Nonempty →
      ∀ l : List M.FactorIndex, (∀ i, l.count i = α i) →
        ∃ F : MvPolynomial (Fin l.length × M.Variable) K, F ≠ 0 ∧
          ∀ c : Fin l.length → M.Variable → K,
            MvPolynomial.eval (Function.uncurry c) F ≠ 0 →
            ({x : M.Point | x ∈ W ∧
              ∀ j : Fin l.length, M.eval (MixedFlag.polynomial M l c j) x = 0}).Finite ∧
            Disjoint {x : M.Point | x ∈ W ∧
              ∀ j : Fin l.length, M.eval (MixedFlag.polynomial M l c j) x = 0} B ∧
            (∀ v : M.Variable → K,
              (∀ i, (fun j : Fin (M.ambientDimension i + 1) => v ⟨i,j⟩) ≠ 0) →
              (∀ P ∈ MixedFlag.ideal M (M.vanishingIdeal W) l c l.length,
                MvPolynomial.eval v P = 0) →
              ((MixedFlag.ideal M (M.vanishingIdeal W) l c l.length).map
                (algebraMap M.CoordinateRing
                  (Localization.AtPrime (MvPolynomial.vanishingIdeal K {v})))).IsRadical) := by
  classical
  intro M W hW hWi α hα hdim B hB hBW hne l hl
  obtain ⟨F, hF, hFc⟩ := hgeometry M W hW hWi α hα hdim B hB hBW hne l hl
  refine ⟨F, hF, ?_⟩
  intro c hc
  obtain ⟨hfinite, hdisjoint, hrad⟩ := hFc c hc
  refine ⟨hfinite, hdisjoint, ?_⟩
  intro v hv _
  have hpivot (i : M.FactorIndex) : ∃ j, v ⟨i,j⟩ ≠ 0 := by
    simpa using Function.ne_iff.mp (hv i)
  choose b hb using hpivot
  exact point_local_of_chart M _ (mixed_ideal_homogeneous M W l c l.length) b
    (hrad b) v hb

end PhilipponMultiplicity.NormalizedChartRadical
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
        ∃ F : MvPolynomial (Fin l.length × M.Variable) K, F ≠ 0 ∧
          ∀ c : Fin l.length → M.Variable → K,
            MvPolynomial.eval (Function.uncurry c) F ≠ 0 →
            ({x : M.Point | x ∈ W ∧
              ∀ j : Fin l.length, M.eval (MixedFlag.polynomial M l c j) x = 0}).Finite ∧
            Disjoint {x : M.Point | x ∈ W ∧
              ∀ j : Fin l.length, M.eval (MixedFlag.polynomial M l c j) x = 0} B ∧
            (∀ v : M.Variable → K,
                (∀ i : M.FactorIndex,
                  (fun j : Fin (M.ambientDimension i + 1) => v ⟨i,j⟩) ≠ 0) →
                (∀ P ∈ MixedFlag.ideal M (M.vanishingIdeal W) l c l.length,
                  MvPolynomial.eval v P = 0) →
                ((MixedFlag.ideal M (M.vanishingIdeal W) l c l.length).map
                  (algebraMap M.CoordinateRing
                    (Localization.AtPrime (MvPolynomial.vanishingIdeal K {v})))).IsRadical) := by
  exact NormalizedChartRadical.reduced_point_sections_of_normalized K hK
    (exists_principal_open_reduced_normalized_mixed_sections K hK)
