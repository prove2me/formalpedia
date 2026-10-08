-- Prove2me | solution 1 for PhilipponMultiplicity.closure_action_has_multilinear_degree_model
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-10-07T05:52:35.900833+00:00
-- url     : https://prove2.me/submissions/9d743feb-91cb-4b6b-818e-e3445cba9b96
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_PhilipponMultiplicity_closure_action_has_homogeneous_degree_polynomials
import Definitions.Def_PhilipponMultiplicity_SectionThree
import Definitions.Def_PhilipponMultiplicity_Support
import Mathlib.Data.Fintype.EquivFin
import Mathlib.LinearAlgebra.Multilinear.Basic
import Mathlib.RingTheory.Finiteness.Cardinality
import Mathlib.RingTheory.MvPolynomial.Homogeneous


section

set_option autoImplicit false
open scoped BigOperators
noncomputable section

namespace HomogeneousDiagonal

variable {R σ : Type*} [CommSemiring R] [Fintype σ]

/-- Enumerate the occurrences of each variable to multilinearize a monomial.
Symmetry is not required, and the empty monomial gives a zero-ary map. -/
theorem monomial (m : σ →₀ ℕ) (d : ℕ) (hm : ∑ i, m i = d) :
    ∃ L : MultilinearMap R (fun _ : Fin d => σ → R) R,
      ∀ x, L (fun _ => x) = ∏ i, x i ^ m i := by
  classical
  have hcard : Fintype.card ((i : σ) × Fin (m i)) = d := by
    simpa using hm
  let e : Fin d ≃ ((i : σ) × Fin (m i)) :=
    (Fintype.equivFinOfCardEq hcard).symm
  refine ⟨(MultilinearMap.mkPiAlgebra R (Fin d) R).compLinearMap
    (fun j => LinearMap.proj (e j).1), ?_⟩
  intro x
  change (∏ j : Fin d, x (e j).1) = _
  rw [Fintype.prod_equiv e (fun j => x (e j).1) (fun j => x j.1) (by intro j; rfl)]
  simp [Fintype.prod_sigma]

/-- Every homogeneous polynomial on a finite free module is the diagonal of a
multilinear map, over any commutative semiring and in every degree. -/
theorem polynomial (P : MvPolynomial σ R) (d : ℕ) (hP : P.IsHomogeneous d) :
    ∃ L : MultilinearMap R (fun _ : Fin d => σ → R) R,
      ∀ x, L (fun _ => x) = MvPolynomial.eval x P := by
  classical
  have hm : ∀ m : P.support, ∑ i, m.val i = d := by
    intro m
    have h := hP.degree_eq_sum_deg_support m.property
    rw [h]
    exact (Finsupp.sum_fintype m.val (fun _ n => n) (by simp)).symm
  choose L hL using fun m : P.support => monomial (R := R) m.val d (hm m)
  refine ⟨∑ m : P.support, P.coeff m.val • L m, ?_⟩
  intro x
  simp only [sum_apply, smul_apply, hL, smul_eq_mul]
  conv_rhs => rw [← P.support_sum_monomial_coeff]
  simp only [map_sum, MvPolynomial.eval_monomial]
  rw [← Finset.sum_coe_sort P.support]
  apply Finset.sum_congr rfl
  intro m _
  congr 1
  exact (Finsupp.prod_fintype m.val (fun i n => x i ^ n) (by simp)).symm

/-- Restrict the rational diagonal form to an integer lattice. -/
theorem integer_lattice (P : MvPolynomial σ ℚ) (d : ℕ) (hP : P.IsHomogeneous d) :
    ∃ L : MultilinearMap ℤ (fun _ : Fin d => σ → ℤ) ℚ,
      ∀ x, L (fun _ => x) = MvPolynomial.eval (fun i => (x i : ℚ)) P := by
  obtain ⟨L,hL⟩ := polynomial P d hP
  let cast : (σ → ℤ) →ₗ[ℤ] (σ → ℚ) :=
    LinearMap.pi (fun i =>
      ((Int.castRingHom ℚ).toAddMonoidHom.toIntLinearMap).comp (LinearMap.proj i))
  refine ⟨(L.restrictScalars ℤ).compLinearMap (fun _ => cast), ?_⟩
  intro x
  exact hL (fun i => (x i : ℚ))

end HomogeneousDiagonal
end

end


section

set_option autoImplicit false
open scoped BigOperators Topology
noncomputable section

namespace PhilipponMultiplicity

theorem multilinear_degree_of_homogeneous_polynomials
    (K : Type*) [NontriviallyNormedField K] (hK : IsPhilipponBaseField K)
    (G : EmbeddedGroupProduct K)
    (τ : G.Point → (groupProjectiveClosure G ≃ groupProjectiveClosure G))
    (hzero : τ 0 = Equiv.refl _)
    (hadd : ∀ g h, τ (g+h) = (τ h).trans (τ g))
    (hregular : ∀ g, G.ambient.IsRegularAlong G.ambient
      (fun x : groupProjectiveClosure G => x.val) (fun x => (τ g x).val))
    (hgeometry : ∃ (m : ℕ)
      (α : Multiplicative G.Point →* ((Fin m → ℤ) ≃ₗ[ℤ] (Fin m → ℤ)))
      (c : G.FactorIndex → (Fin m → ℤ)),
      ∀ (V : Set (groupProjectiveClosure G)),
        @IsClosed _ (TopologicalSpace.induced Subtype.val G.ambient.zariskiTopology) V →
        ∃ P : MvPolynomial (Fin m) ℚ,
          P.IsHomogeneous (SectionThree.locusDimension G.ambient (Subtype.val '' V)) ∧
          ∀ (g : G.Point) (D : G.FactorIndex → ℕ), (∀ i, 1 ≤ D i) →
            SectionThree.locusDegreeValue G.ambient (Subtype.val '' (τ g '' V)) D =
              MvPolynomial.eval
                (fun j => (α (Multiplicative.ofAdd (-g)) (∑ i, (D i : ℤ) • c i) j : ℚ)) P) :
    ∃ (A : Type) (_ : AddCommGroup A) (_ : Module ℤ A)
      (_ : Module.Finite ℤ A) (α : Multiplicative G.Point →* (A ≃ₗ[ℤ] A))
      (c : G.FactorIndex → A),
      ∀ (V : Set (groupProjectiveClosure G)),
        @IsClosed _ (TopologicalSpace.induced Subtype.val G.ambient.zariskiTopology) V →
        ∃ I : MultilinearMap ℤ
          (fun _ : Fin (SectionThree.locusDimension G.ambient (Subtype.val '' V)) => A) ℚ,
          ∀ (g : G.Point) (D : G.FactorIndex → ℕ), (∀ i, 1 ≤ D i) →
            SectionThree.locusDegreeValue G.ambient (Subtype.val '' (τ g '' V)) D =
              I (fun _ => α (Multiplicative.ofAdd (-g)) (∑ i, (D i : ℤ) • c i)) := by
  classical
  obtain ⟨m, α, c, h⟩ := hgeometry
  refine ⟨(Fin m → ℤ), inferInstance, inferInstance, inferInstance, α, c, ?_⟩
  intro V hV
  obtain ⟨P, hP, hdegree⟩ := h V hV
  obtain ⟨I, hI⟩ := HomogeneousDiagonal.integer_lattice P _ hP
  refine ⟨I, ?_⟩
  intro g D hD
  exact (hdegree g D hD).trans (hI _).symm

end PhilipponMultiplicity
end

end

set_option autoImplicit false
open PhilipponMultiplicity
open scoped BigOperators Topology

theorem solution
    (K : Type*) [NontriviallyNormedField K] (hK : IsPhilipponBaseField K)
    (G : EmbeddedGroupProduct K)
    (τ : G.Point → (groupProjectiveClosure G ≃ groupProjectiveClosure G))
    (hzero : τ 0 = Equiv.refl _)
    (hadd : ∀ g h, τ (g+h) = (τ h).trans (τ g))
    (hregular : ∀ g, G.ambient.IsRegularAlong G.ambient
      (fun x : groupProjectiveClosure G => x.val) (fun x => (τ g x).val)) :
    ∃ (A : Type) (_ : AddCommGroup A) (_ : Module ℤ A)
      (_ : Module.Finite ℤ A) (α : Multiplicative G.Point →* (A ≃ₗ[ℤ] A))
      (c : G.FactorIndex → A),
      ∀ (V : Set (groupProjectiveClosure G)),
        @IsClosed _ (TopologicalSpace.induced Subtype.val G.ambient.zariskiTopology) V →
        ∃ I : MultilinearMap ℤ
          (fun _ : Fin (SectionThree.locusDimension G.ambient (Subtype.val '' V)) => A) ℚ,
          ∀ (g : G.Point) (D : G.FactorIndex → ℕ), (∀ i, 1 ≤ D i) →
            SectionThree.locusDegreeValue G.ambient (Subtype.val '' (τ g '' V)) D =
              I (fun _ => α (Multiplicative.ofAdd (-g)) (∑ i, (D i : ℤ) • c i)) := by
  exact multilinear_degree_of_homogeneous_polynomials K hK G τ hzero hadd hregular
    (closure_action_has_homogeneous_degree_polynomials K hK G τ hzero hadd hregular)
