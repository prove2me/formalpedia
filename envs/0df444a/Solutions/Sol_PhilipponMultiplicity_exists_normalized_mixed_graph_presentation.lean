-- Prove2me | solution 1 for PhilipponMultiplicity.exists_normalized_mixed_graph_presentation
-- status  : ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-10-08T07:39:30.06999+00:00
-- url     : https://prove2.me/submissions/779df56f-282b-4964-8a0d-3037ca2af448

import Theorems.Thm_PhilipponMultiplicity_normalized_principal_chart_domain_and_dimension
import Definitions.Def_PhilipponMultiplicity_GeometricSupport
import Definitions.Def_PhilipponMultiplicity_MixedFlagParameters
import Definitions.Def_PhilipponMultiplicity_UniversalMixedSlices
import Mathlib


section

set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section

namespace PhilipponMultiplicity.CoefficientElimination
open MvPolynomial

variable {R ι τ : Type*} [CommRing R]

def ideal (g : ι → MvPolynomial τ R) : Ideal (MvPolynomial (ι ⊕ τ) R) :=
  Ideal.span (Set.range (fun i => X (Sum.inl i) - rename Sum.inr (g i)))

def evaluate (g : ι → MvPolynomial τ R) :
    MvPolynomial (ι ⊕ τ) R →ₐ[R] MvPolynomial τ R :=
  aeval (Sum.elim g X)

@[simp] theorem evaluate_rename (g : ι → MvPolynomial τ R) (p : MvPolynomial τ R) :
    evaluate g (rename Sum.inr p) = p := by
  have h : (evaluate g).comp (rename Sum.inr) = AlgHom.id R _ := by
    ext t
    simp [evaluate]
  exact DFunLike.congr_fun h p

theorem ideal_le_ker_evaluate (g : ι → MvPolynomial τ R) :
    ideal g ≤ RingHom.ker (evaluate g).toRingHom := by
  apply Ideal.span_le.mpr
  rintro _ ⟨i, rfl⟩
  change evaluate g (X (Sum.inl i) - rename Sum.inr (g i)) = 0
  rw [map_sub, evaluate_rename]
  simp [evaluate]

def toFree (g : ι → MvPolynomial τ R) :
    (MvPolynomial (ι ⊕ τ) R ⧸ ideal g) →ₐ[R] MvPolynomial τ R :=
  Ideal.Quotient.liftₐ (ideal g) (evaluate g) (ideal_le_ker_evaluate g)

def fromFree (g : ι → MvPolynomial τ R) :
    MvPolynomial τ R →ₐ[R] (MvPolynomial (ι ⊕ τ) R ⧸ ideal g) :=
  (Ideal.Quotient.mkₐ R (ideal g)).comp (rename Sum.inr)

@[simp] theorem toFree_mk (g : ι → MvPolynomial τ R) (p : MvPolynomial (ι ⊕ τ) R) :
    toFree g (Ideal.Quotient.mk (ideal g) p) = evaluate g p := rfl

theorem toFree_fromFree (g : ι → MvPolynomial τ R) :
    (toFree g).comp (fromFree g) = AlgHom.id R _ := by
  ext t
  simp [fromFree, evaluate]

theorem fromFree_toFree (g : ι → MvPolynomial τ R) :
    (fromFree g).comp (toFree g) = AlgHom.id R _ := by
  apply Ideal.Quotient.algHom_ext
  ext t
  cases t with
  | inl i =>
      have hrel : Ideal.Quotient.mk (ideal g)
          (X (Sum.inl i) - rename Sum.inr (g i)) = 0 :=
        Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (Set.mem_range_self i))
      have h : Ideal.Quotient.mk (ideal g) (X (Sum.inl i)) =
          Ideal.Quotient.mk (ideal g) (rename Sum.inr (g i)) := by
        simpa only [map_sub, sub_eq_zero] using hrel
      simpa [fromFree, evaluate] using h.symm
  | inr t => simp [fromFree, evaluate]

/-- Independent monic graph equations eliminate their distinguished variables
over an arbitrary commutative ring, without taking a radical. -/
def quotientEquiv (g : ι → MvPolynomial τ R) :
    (MvPolynomial (ι ⊕ τ) R ⧸ ideal g) ≃ₐ[R] MvPolynomial τ R :=
  AlgEquiv.ofAlgHom (toFree g) (fromFree g) (toFree_fromFree g) (fromFree_toFree g)

theorem quotient_domain (g : ι → MvPolynomial τ R) [IsDomain R] :
    IsDomain (MvPolynomial (ι ⊕ τ) R ⧸ ideal g) :=
  (quotientEquiv g).injective.isDomain

theorem quotient_dimension (g : ι → MvPolynomial τ R)
    [IsNoetherianRing R] [Finite τ] :
    ringKrullDim (MvPolynomial (ι ⊕ τ) R ⧸ ideal g) = ringKrullDim R + Nat.card τ := by
  rw [(quotientEquiv g).toRingEquiv.ringKrullDim,
    MvPolynomial.ringKrullDim_of_isNoetherianRing]

end PhilipponMultiplicity.CoefficientElimination
end

end


section

set_option autoImplicit false
set_option maxHeartbeats 20000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open scoped BigOperators
noncomputable section

namespace PhilipponMultiplicity.MixedChartEquivalence
open MvPolynomial
variable {K : Type*} [Field K] (M : MultiProjectiveSpace K)
    (W : Set M.Point) (l : List M.FactorIndex)
    (b : ∀ i : M.FactorIndex, Fin (M.ambientDimension i + 1)) (H : M.CoordinateRing)

def baseIdeal : Ideal (Polynomial M.CoordinateRing) :=
  ((M.vanishingIdeal W ⊔ Ideal.span (Set.range (fun i : M.FactorIndex =>
    (X (⟨i,b i⟩ : M.Variable) : M.CoordinateRing) - 1))).map Polynomial.C) ⊔
    Ideal.span {Polynomial.C H * Polynomial.X - 1}

abbrev Base := Polynomial M.CoordinateRing ⧸ baseIdeal M W b H
abbrev Free := {t : Fin l.length × M.Variable //
  t.2 ≠ (⟨l[t.1],b l[t.1]⟩ : M.Variable)}

def baseToIncidence : Base M W b H →+* MixedFamily.CoordinateRing M W l b H :=
  Ideal.Quotient.lift (baseIdeal M W b H)
    ((Ideal.Quotient.mk (MixedFamily.ideal M W l b H)).comp C) (by
      intro P hP
      apply Ideal.Quotient.eq_zero_iff_mem.mpr
      have hi : (baseIdeal M W b H).map C ≤ MixedFamily.ideal M W l b H := by
        simp only [baseIdeal, Ideal.map_sup, Ideal.map_map, Ideal.map_span,
          Set.image_singleton, MixedFamily.ideal, MixedFamily.fixed,
          Set.image_image, RingHom.coe_comp]
        exact sup_le_sup (sup_le_sup le_sup_left le_rfl) le_rfl
      exact hi (Ideal.mem_map_of_mem C hP))

@[simp] theorem baseToIncidence_mk (P : Polynomial M.CoordinateRing) :
    baseToIncidence M W l b H (Ideal.Quotient.mk (baseIdeal M W b H) P) =
      Ideal.Quotient.mk (MixedFamily.ideal M W l b H) (C P) := rfl

theorem base_pivot (i : M.FactorIndex) :
    Ideal.Quotient.mk (baseIdeal M W b H)
      (Polynomial.C (X (⟨i,b i⟩ : M.Variable))) = 1 := by
  apply sub_eq_zero.mp
  rw [← map_one (Ideal.Quotient.mk _), ← map_sub, ← Polynomial.C_1, ← map_sub]
  apply Ideal.Quotient.eq_zero_iff_mem.mpr
  apply Ideal.mem_sup_left
  apply Ideal.mem_map_of_mem
  exact Ideal.mem_sup_right (Ideal.subset_span (Set.mem_range_self i))

end PhilipponMultiplicity.MixedChartEquivalence
end

end


section

set_option autoImplicit false
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open scoped BigOperators
noncomputable section

namespace PhilipponMultiplicity.MixedChartEquivalence
open MvPolynomial
variable {K : Type*} [Field K] (M : MultiProjectiveSpace K)
    (W : Set M.Point) (l : List M.FactorIndex)
    (b : ∀ i : M.FactorIndex, Fin (M.ambientDimension i + 1)) (H : M.CoordinateRing)

def fromFree : MvPolynomial (Free M l b) (Base M W b H) →+*
    MixedFamily.CoordinateRing M W l b H :=
  eval₂Hom (baseToIncidence M W l b H)
    (fun t => Ideal.Quotient.mk (MixedFamily.ideal M W l b H) (X t.val))

def freeIndex (j : Fin l.length)
    (t : {t : Fin (M.ambientDimension l[j] + 1) // t ≠ b l[j]}) : Free M l b :=
  ⟨(j,(⟨l[j],t.val⟩ : M.Variable)), by
    change (Sigma.mk l[j] t.val : M.Variable) ≠ Sigma.mk l[j] (b l[j])
    intro h
    exact t.property (eq_of_heq (Sigma.mk.inj_iff.mp h).2)⟩

def graph (j : Fin l.length) : MvPolynomial (Free M l b) (Base M W b H) :=
  - ∑ t : {t : Fin (M.ambientDimension l[j] + 1) // t ≠ b l[j]},
    X (freeIndex M l b j t) *
      C (Ideal.Quotient.mk (baseIdeal M W b H)
        (Polynomial.C (X (⟨l[j],t.val⟩ : M.Variable))))

def coefficient (t : Fin l.length × M.Variable) :
    MvPolynomial (Free M l b) (Base M W b H) :=
  if h : t.2 = (⟨l[t.1],b l[t.1]⟩ : M.Variable) then graph M W l b H t.1
  else X ⟨t,h⟩

def evaluate : MixedFamily.TotalPolynomial M l →+*
    MvPolynomial (Free M l b) (Base M W b H) :=
  eval₂Hom (C.comp (Ideal.Quotient.mk (baseIdeal M W b H)))
    (coefficient M W l b H)

@[simp] theorem evaluate_C (P : Polynomial M.CoordinateRing) :
    evaluate M W l b H (C P) = C (Ideal.Quotient.mk (baseIdeal M W b H) P) :=
  eval₂Hom_C _ _ _

@[simp] theorem evaluate_X (t : Fin l.length × M.Variable) :
    evaluate M W l b H (X t) = coefficient M W l b H t := eval₂Hom_X' _ _ _

@[simp] theorem coefficient_pivot (j : Fin l.length) :
    coefficient M W l b H (j,(⟨l[j],b l[j]⟩ : M.Variable)) = graph M W l b H j := by
  simp [coefficient]

@[simp] theorem coefficient_free (t : Free M l b) :
    coefficient M W l b H t.val = X t := by
  rw [coefficient, dif_neg t.property]

theorem evaluate_row (j : Fin l.length) :
    evaluate M W l b H (MixedFamily.row M l j) = 0 := by
  classical
  simp only [MixedFamily.row, map_sum, map_mul, evaluate_X, MixedFamily.fixed,
    RingHom.comp_apply, evaluate_C]
  rw [Fintype.sum_eq_add_sum_subtype_ne _ (b l[j])]
  simp only [coefficient_pivot, base_pivot, map_one, mul_one]
  have ht (t : {t : Fin (M.ambientDimension l[j] + 1) // t ≠ b l[j]}) :
      (⟨l[j],t.val⟩ : M.Variable) ≠ ⟨l[j],b l[j]⟩ := by
    exact (freeIndex M l b j t).property
  simp only [coefficient, dif_neg (ht _), graph, freeIndex]
  exact neg_add_cancel _

theorem ideal_le_ker_evaluate :
    MixedFamily.ideal M W l b H ≤ RingHom.ker (evaluate M W l b H) := by
  have hbase (P : Polynomial M.CoordinateRing) (hP : P ∈ baseIdeal M W b H) :
      evaluate M W l b H (C P) = 0 := by
    rw [evaluate_C, Ideal.Quotient.eq_zero_iff_mem.mpr hP, map_zero]
  rw [MixedFamily.ideal, sup_le_iff, sup_le_iff, sup_le_iff]
  refine ⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩
  · rw [Ideal.map_le_iff_le_comap]
    intro P hP
    apply hbase
    exact Ideal.mem_sup_left
      (Ideal.mem_map_of_mem Polynomial.C (Ideal.mem_sup_left hP))
  · refine iSup_le fun j => iSup_le fun _ => Ideal.span_le.mpr ?_
    rintro P rfl
    exact evaluate_row M W l b H j
  · rw [Ideal.map_le_iff_le_comap]
    intro P hP
    apply hbase
    exact Ideal.mem_sup_left
      (Ideal.mem_map_of_mem Polynomial.C (Ideal.mem_sup_right hP))
  · apply Ideal.span_le.mpr
    rintro P rfl
    apply hbase
    exact Ideal.mem_sup_right (Ideal.subset_span (Set.mem_singleton _))

def toFree : MixedFamily.CoordinateRing M W l b H →+*
    MvPolynomial (Free M l b) (Base M W b H) :=
  Ideal.Quotient.lift (MixedFamily.ideal M W l b H) (evaluate M W l b H)
    (ideal_le_ker_evaluate M W l b H)

@[simp] theorem toFree_mk (P : MixedFamily.TotalPolynomial M l) :
    toFree M W l b H (Ideal.Quotient.mk (MixedFamily.ideal M W l b H) P) =
      evaluate M W l b H P := rfl

end PhilipponMultiplicity.MixedChartEquivalence
end

end


section

set_option autoImplicit false
set_option maxHeartbeats 150000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open scoped BigOperators
noncomputable section

namespace PhilipponMultiplicity.MixedChartEquivalence
open MvPolynomial
variable {K : Type*} [Field K] (M : MultiProjectiveSpace K)
    (W : Set M.Point) (l : List M.FactorIndex)
    (b : ∀ i : M.FactorIndex, Fin (M.ambientDimension i + 1)) (H : M.CoordinateRing)

theorem fromFree_graph (j : Fin l.length) :
    fromFree M W l b H (graph M W l b H j) =
      Ideal.Quotient.mk (MixedFamily.ideal M W l b H)
        (X (j,(⟨l[j],b l[j]⟩ : M.Variable))) := by
  classical
  let q := Ideal.Quotient.mk (MixedFamily.ideal M W l b H)
  have hrow : q (MixedFamily.row M l j) = 0 := by
    apply Ideal.Quotient.eq_zero_iff_mem.mpr
    apply Ideal.mem_sup_left
    apply Ideal.mem_sup_left
    apply Ideal.mem_sup_right
    have hle : Ideal.span {MixedFamily.row M l j} ≤
        ⨆ k : Fin l.length, ⨆ (_ : k.val < l.length), Ideal.span {MixedFamily.row M l k} :=
      le_iSup_of_le j (le_iSup_of_le j.isLt le_rfl)
    exact hle (Ideal.subset_span (Set.mem_singleton _))
  have hp : q (MixedFamily.fixed M l (X (⟨l[j],b l[j]⟩ : M.Variable))) = 1 := by
    have h := congrArg (baseToIncidence M W l b H) (base_pivot M W b H l[j])
    simpa only [baseToIncidence_mk, map_one, MixedFamily.fixed, RingHom.comp_apply, q] using h
  simp only [MixedFamily.row, map_sum, map_mul] at hrow
  rw [Fintype.sum_eq_add_sum_subtype_ne _ (b l[j]), hp, mul_one] at hrow
  have hn := (eq_neg_of_add_eq_zero_left hrow).symm
  simpa only [graph, map_neg, map_sum, map_mul, fromFree, eval₂Hom_C, eval₂Hom_X',
    freeIndex, baseToIncidence_mk, MixedFamily.fixed, RingHom.comp_apply] using hn

theorem fromFree_coefficient (t : Fin l.length × M.Variable) :
    fromFree M W l b H (coefficient M W l b H t) =
      Ideal.Quotient.mk (MixedFamily.ideal M W l b H) (X t) := by
  rw [coefficient]
  split_ifs with ht
  · rw [fromFree_graph]
    have he : (t.1,(⟨l[t.1],b l[t.1]⟩ : M.Variable)) = t := Prod.ext rfl ht.symm
    rw [he]
  · exact eval₂Hom_X' _ _ _

theorem fromFree_toFree :
    (fromFree M W l b H).comp (toFree M W l b H) = RingHom.id _ := by
  apply Ideal.Quotient.ringHom_ext
  apply MvPolynomial.ringHom_ext
  · intro P
    simp only [RingHom.comp_apply, RingHom.id_apply, toFree_mk, evaluate_C,
      fromFree, eval₂Hom_C, baseToIncidence_mk]
  · intro t
    simp only [RingHom.comp_apply, RingHom.id_apply, toFree_mk, evaluate_X,
      fromFree_coefficient]

theorem toFree_baseToIncidence (a : Base M W b H) :
    toFree M W l b H (baseToIncidence M W l b H a) = C a := by
  obtain ⟨P,rfl⟩ := Ideal.Quotient.mk_surjective a
  rw [baseToIncidence_mk, toFree_mk, evaluate_C]

theorem toFree_fromFree :
    (toFree M W l b H).comp (fromFree M W l b H) = RingHom.id _ := by
  apply MvPolynomial.ringHom_ext
  · intro a
    simp only [RingHom.comp_apply, RingHom.id_apply, fromFree, eval₂Hom_C,
      toFree_baseToIncidence]
  · intro t
    simp only [RingHom.comp_apply, RingHom.id_apply, fromFree, eval₂Hom_X',
      toFree_mk, evaluate_X, coefficient_free]

def polynomialEquiv : MixedFamily.CoordinateRing M W l b H ≃+*
    MvPolynomial (Free M l b) (Base M W b H) :=
  RingEquiv.ofRingHom (toFree M W l b H) (fromFree M W l b H)
    (toFree_fromFree M W l b H) (fromFree_toFree M W l b H)

def graphEquiv : MixedFamily.CoordinateRing M W l b H ≃+*
    (MvPolynomial (Fin l.length ⊕ Free M l b) (Base M W b H) ⧸
      CoefficientElimination.ideal (graph M W l b H)) :=
  (polynomialEquiv M W l b H).trans
    (CoefficientElimination.quotientEquiv (graph M W l b H)).toRingEquiv.symm

theorem base_nontrivial [Nontrivial (MixedFamily.CoordinateRing M W l b H)] :
    Nontrivial (Base M W b H) :=
  (baseToIncidence M W l b H).domain_nontrivial

theorem base_finiteType : Algebra.FiniteType K (Base M W b H) := by
  infer_instance

end PhilipponMultiplicity.MixedChartEquivalence
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

theorem graph_presentation_of_normalized_chart
    (K : Type u) [NontriviallyNormedField K] (hK : IsPhilipponBaseField K)
    (hchart : ∀ (M : MultiProjectiveSpace K) (W : Set M.Point),
      @IsClosed _ M.zariskiTopology W → @IsIrreducible _ M.zariskiTopology W →
      ∀ b : ∀ i : M.FactorIndex, Fin (M.ambientDimension i + 1),
      ∀ H : M.CoordinateRing,
        let A := (Polynomial M.CoordinateRing) ⧸
          (((M.vanishingIdeal W ⊔ Ideal.span (Set.range (fun i : M.FactorIndex =>
            (MvPolynomial.X (⟨i,b i⟩ : M.Variable) : M.CoordinateRing) - 1))).map
              Polynomial.C) ⊔ Ideal.span {Polynomial.C H * Polynomial.X - 1})
        Nontrivial A → IsDomain A ∧ ringKrullDim A = locusDimension M W) :
    ∀ (M : MultiProjectiveSpace K) (W : Set M.Point),
      @IsClosed _ M.zariskiTopology W → @IsIrreducible _ M.zariskiTopology W →
      ∀ (α : M.FactorIndex → ℕ), (∀ i, α i ≤ M.ambientDimension i) →
      (∑ i, α i = locusDimension M W) →
      ∀ l : List M.FactorIndex, (∀ i, l.count i = α i) →
      ∀ b : ∀ i : M.FactorIndex, Fin (M.ambientDimension i + 1),
      ∀ H : M.CoordinateRing,
        Nontrivial (MixedFamily.CoordinateRing M W l b H) →
        let F := {t : Fin l.length × M.Variable //
          t.2 ≠ (⟨l[t.1], b l[t.1]⟩ : M.Variable)}
        ∃ (A : Type u) (instA : CommRing A) (algA : Algebra K A),
          IsDomain A ∧ Algebra.FiniteType K A ∧
          ringKrullDim A = locusDimension M W ∧
          ∃ g : Fin l.length → MvPolynomial F A,
            Nonempty (MixedFamily.CoordinateRing M W l b H ≃+*
              (MvPolynomial (Fin l.length ⊕ F) A ⧸
                Ideal.span (Set.range (fun j =>
                  (MvPolynomial.X (Sum.inl j) : MvPolynomial (Fin l.length ⊕ F) A) -
                    MvPolynomial.rename Sum.inr (g j))))) := by
  intro M W hW hirr α hα hdim l hl b H hnon
  letI := hnon
  have hA_nontrivial := MixedChartEquivalence.base_nontrivial M W l b H
  obtain ⟨hdom, hA_dim⟩ := hchart M W hW hirr b H hA_nontrivial
  refine ⟨MixedChartEquivalence.Base M W b H, inferInstance, inferInstance,
    hdom, MixedChartEquivalence.base_finiteType M W b H, hA_dim, ?_⟩
  exact ⟨MixedChartEquivalence.graph M W l b H,
    ⟨MixedChartEquivalence.graphEquiv M W l b H⟩⟩

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
      ∀ (α : M.FactorIndex → ℕ), (∀ i, α i ≤ M.ambientDimension i) →
      (∑ i, α i = locusDimension M W) →
      ∀ l : List M.FactorIndex, (∀ i, l.count i = α i) →
      ∀ b : ∀ i : M.FactorIndex, Fin (M.ambientDimension i + 1),
      ∀ H : M.CoordinateRing,
        Nontrivial (MixedFamily.CoordinateRing M W l b H) →
        let F := {t : Fin l.length × M.Variable //
          t.2 ≠ (⟨l[t.1], b l[t.1]⟩ : M.Variable)}
        ∃ (A : Type u) (instA : CommRing A) (algA : Algebra K A),
          IsDomain A ∧ Algebra.FiniteType K A ∧
          ringKrullDim A = locusDimension M W ∧
          ∃ g : Fin l.length → MvPolynomial F A,
            Nonempty (MixedFamily.CoordinateRing M W l b H ≃+*
              (MvPolynomial (Fin l.length ⊕ F) A ⧸
                Ideal.span (Set.range (fun j =>
                  (MvPolynomial.X (Sum.inl j) : MvPolynomial (Fin l.length ⊕ F) A) -
                    MvPolynomial.rename Sum.inr (g j))))) := by
  exact graph_presentation_of_normalized_chart K hK
    (normalized_principal_chart_domain_and_dimension K hK)
