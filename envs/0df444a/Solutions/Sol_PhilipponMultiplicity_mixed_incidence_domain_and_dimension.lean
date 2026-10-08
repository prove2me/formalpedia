-- Prove2me | solution 1 for PhilipponMultiplicity.mixed_incidence_domain_and_dimension
-- status  : ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-10-08T07:01:17.081532+00:00
-- url     : https://prove2.me/submissions/2b8b4c80-a812-46f3-b938-ee7d2333ceef

import Theorems.Thm_PhilipponMultiplicity_exists_normalized_mixed_graph_presentation
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
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open scoped BigOperators
noncomputable section

namespace PhilipponMultiplicity.MixedGraphDimension
open SectionThree

theorem card_free_add {ι σ : Type*} [Fintype ι] [Fintype σ] (p : ι → σ) :
    Nat.card {t : ι × σ // t.2 ≠ p t.1} + Nat.card ι = Nat.card (ι × σ) := by
  classical
  let e : {t : ι × σ // t.2 = p t.1} ≃ ι := {
    toFun := fun t => t.val.1
    invFun := fun i => ⟨(i, p i), rfl⟩
    left_inv := by
      rintro ⟨⟨i,s⟩,h⟩
      change s = p i at h
      subst s
      rfl
    right_inv := fun _ => rfl }
  have hp := Fintype.card_congr e
  simp only [Nat.card_eq_fintype_card]
  rw [Fintype.card_subtype_compl, hp]
  apply Nat.sub_add_cancel
  rw [← hp]
  exact Fintype.card_subtype_le _

theorem length_eq_sum_counts {ι : Type*} [Fintype ι] [DecidableEq ι] (l : List ι) :
    l.length = ∑ i, l.count i := by
  classical
  induction l with
  | nil => simp
  | cons a l ih => simp [List.count_cons, Finset.sum_add_distrib, ← ih]

abbrev Free {K : Type*} [Field K] (M : MultiProjectiveSpace K)
    (l : List M.FactorIndex)
    (b : ∀ i : M.FactorIndex, Fin (M.ambientDimension i + 1)) :=
  {t : Fin l.length × M.Variable // t.2 ≠ (⟨l[t.1],b l[t.1]⟩ : M.Variable)}

theorem domain_and_dimension_of_graph
    {K : Type*} [Field K] (M : MultiProjectiveSpace K) (W : Set M.Point)
    (l : List M.FactorIndex)
    (b : ∀ i : M.FactorIndex, Fin (M.ambientDimension i + 1))
    (H : M.CoordinateRing) (hlength : l.length = locusDimension M W)
    (A : Type*) [CommRing A] [Algebra K A] [IsDomain A] [Algebra.FiniteType K A]
    (hA : ringKrullDim A = locusDimension M W)
    (g : Fin l.length → MvPolynomial (Free M l b) A)
    (e : MixedFamily.CoordinateRing M W l b H ≃+*
      (MvPolynomial (Fin l.length ⊕ Free M l b) A ⧸ CoefficientElimination.ideal g)) :
    IsDomain (MixedFamily.CoordinateRing M W l b H) ∧
    ringKrullDim (MixedFamily.CoordinateRing M W l b H) =
      Nat.card (Fin l.length × M.Variable) := by
  classical
  let : IsNoetherianRing A := Algebra.FiniteType.isNoetherianRing K A
  let := CoefficientElimination.quotient_domain g
  refine ⟨e.injective.isDomain, ?_⟩
  rw [e.ringKrullDim, CoefficientElimination.quotient_dimension, hA, ← hlength]
  have hc := card_free_add (σ := M.Variable)
    (fun j : Fin l.length => (⟨l[j],b l[j]⟩ : M.Variable))
  simp only [Nat.card_fin] at hc
  change Nat.card (Free M l b) + l.length = Nat.card (Fin l.length × M.Variable) at hc
  have hc' := (Nat.add_comm l.length (Nat.card (Free M l b))).trans hc
  exact_mod_cast hc'

end PhilipponMultiplicity.MixedGraphDimension
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

theorem mixed_incidence_dimension_of_graph_presentation
    (K : Type u) [NontriviallyNormedField K] (hK : IsPhilipponBaseField K)
    (hgraph : ∀ (M : MultiProjectiveSpace K) (W : Set M.Point),
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
                    MvPolynomial.rename Sum.inr (g j)))))) :
    ∀ (M : MultiProjectiveSpace K) (W : Set M.Point),
      @IsClosed _ M.zariskiTopology W → @IsIrreducible _ M.zariskiTopology W →
      ∀ (α : M.FactorIndex → ℕ), (∀ i, α i ≤ M.ambientDimension i) →
      (∑ i, α i = locusDimension M W) →
      ∀ l : List M.FactorIndex, (∀ i, l.count i = α i) →
      ∀ b : ∀ i : M.FactorIndex, Fin (M.ambientDimension i + 1),
      ∀ H : M.CoordinateRing,
        Nontrivial (MixedFamily.CoordinateRing M W l b H) →
        IsDomain (MixedFamily.CoordinateRing M W l b H) ∧
        ringKrullDim (MixedFamily.CoordinateRing M W l b H) =
          Nat.card (Fin l.length × M.Variable) := by
  intro M W hW hirr α hα hdim l hl b H hnon
  obtain ⟨A, instA, algA, hdom, hfinite, hA, g, ⟨e⟩⟩ :=
    hgraph M W hW hirr α hα hdim l hl b H hnon
  letI := instA
  letI := algA
  letI := hdom
  letI := hfinite
  have hlength : l.length = locusDimension M W := calc
    l.length = ∑ i, l.count i := MixedGraphDimension.length_eq_sum_counts l
    _ = ∑ i, α i := Finset.sum_congr rfl (fun i _ => hl i)
    _ = locusDimension M W := hdim
  exact MixedGraphDimension.domain_and_dimension_of_graph M W l b H hlength A hA g e

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
        Nontrivial (MixedFamily.CoordinateRing M W l b H) →
        IsDomain (MixedFamily.CoordinateRing M W l b H) ∧
        ringKrullDim (MixedFamily.CoordinateRing M W l b H) =
          Nat.card (Fin l.length × M.Variable) := by
  exact mixed_incidence_dimension_of_graph_presentation K hK
    (exists_normalized_mixed_graph_presentation K hK)
