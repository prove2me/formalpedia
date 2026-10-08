-- Prove2me | solution 1 for PhilipponMultiplicity.closure_action_has_homogeneous_degree_polynomials
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-10-07T07:18:07.748601+00:00
-- url     : https://prove2.me/submissions/14fe7777-1d68-41be-ab2a-0a72559f863c
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_PhilipponMultiplicity_closure_action_has_dimension_preserving_polynomial_model
import Definitions.Def_PhilipponMultiplicity_SectionThree
import Definitions.Def_PhilipponMultiplicity_Support
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Data.Fintype.EquivFin
import Mathlib.LinearAlgebra.Multilinear.Basic
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
open scoped BigOperators
noncomputable section

namespace HomogeneousExtraction
variable {R σ : Type*} [Field R] [CharZero R] [Fintype σ]

/-- Scaling every coordinate of a homogeneous polynomial scales its value by
the corresponding power, also in degree zero. -/
theorem eval_scale (P : MvPolynomial σ R) (d : ℕ) (hP : P.IsHomogeneous d)
    (x : σ → R) (t : R) :
    MvPolynomial.eval (fun i => t * x i) P = t ^ d * MvPolynomial.eval x P := by
  obtain ⟨L,hL⟩ := HomogeneousDiagonal.polynomial P d hP
  have h := L.map_smul_univ (fun _ => t) (fun _ => x)
  have hx : t • x = (fun i => t * x i) := rfl
  simpa only [hx, smul_eq_mul, Finset.prod_const,
    Finset.card_univ, Fintype.card_fin, hL] using h

/-- Restrict a multivariate polynomial to the line through an arbitrary vector. -/
theorem ray_eval (P : MvPolynomial σ R) (x : σ → R) (t : R) :
    Polynomial.eval t
      (MvPolynomial.eval₂ Polynomial.C (fun i => Polynomial.C (x i) * Polynomial.X) P) =
        MvPolynomial.eval (fun i => t * x i) P := by
  change (Polynomial.evalRingHom t) (MvPolynomial.eval₂ Polynomial.C
    (fun i => Polynomial.C (x i) * Polynomial.X) P) = _
  rw [MvPolynomial.eval₂_comp_left]
  have hc : (Polynomial.evalRingHom t).comp Polynomial.C = RingHom.id R := by
    ext r
    simp
  rw [hc, MvPolynomial.eval₂_id]
  have hf : (⇑(Polynomial.evalRingHom t) ∘
      (fun i => Polynomial.C (x i) * Polynomial.X)) = (fun i => t * x i) := by
    funext i
    change Polynomial.eval t (Polynomial.C (x i) * Polynomial.X) = t * x i
    rw [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X, mul_comm]
  rw [hf]

/-- The coefficient of each power on a ray is the corresponding homogeneous
component evaluated at the direction vector. No coordinates must be nonzero. -/
theorem ray_eq_sum (P : MvPolynomial σ R) (x : σ → R) :
    MvPolynomial.eval₂ Polynomial.C (fun i => Polynomial.C (x i) * Polynomial.X) P =
      ∑ n ∈ Finset.range (P.totalDegree + 1),
        Polynomial.monomial n (MvPolynomial.eval x (MvPolynomial.homogeneousComponent n P)) := by
  apply Polynomial.funext
  intro t
  rw [ray_eval]
  simp only [Polynomial.eval_finsetSum, Polynomial.eval_monomial]
  calc
    MvPolynomial.eval (fun i => t * x i) P =
        ∑ n ∈ Finset.range (P.totalDegree + 1),
          MvPolynomial.eval (fun i => t * x i) (MvPolynomial.homogeneousComponent n P) := by
            rw [← map_sum, MvPolynomial.sum_homogeneousComponent]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro n _
      rw [eval_scale _ n (MvPolynomial.homogeneousComponent_isHomogeneous _ _)]
      exact mul_comm _ _

theorem ray_coeff (P : MvPolynomial σ R) (x : σ → R) (d : ℕ) :
    (MvPolynomial.eval₂ Polynomial.C
      (fun i => Polynomial.C (x i) * Polynomial.X) P).coeff d =
        MvPolynomial.eval x (MvPolynomial.homogeneousComponent d P) := by
  classical
  rw [ray_eq_sum, Polynomial.finsetSum_coeff]
  simp only [Polynomial.coeff_monomial]
  by_cases hd : d < P.totalDegree + 1
  · simp [Finset.mem_range, hd]
  · have hlt : P.totalDegree < d := by omega
    simp [Finset.mem_range, hd, MvPolynomial.homogeneousComponent_eq_zero d P hlt]

/-- Positive integral dilations suffice to isolate a prescribed homogeneous
component. Other components may exist but vanish at the given direction. -/
theorem component_eval_of_scaling (P : MvPolynomial σ R) (x : σ → R) (d : ℕ)
    (hscale : ∀ n : ℕ, 0 < n →
      MvPolynomial.eval (fun i => (n : R) * x i) P =
        (n : R) ^ d * MvPolynomial.eval x P) :
    MvPolynomial.eval x (MvPolynomial.homogeneousComponent d P) =
      MvPolynomial.eval x P := by
  have heq : MvPolynomial.eval₂ Polynomial.C
      (fun i => Polynomial.C (x i) * Polynomial.X) P =
      Polynomial.monomial d (MvPolynomial.eval x P) := by
    apply Polynomial.eq_of_infinite_eval_eq
    have hinj : Function.Injective (fun n : ℕ => ((n + 1 : ℕ) : R)) := by
      intro a b h
      exact Nat.add_right_cancel (Nat.cast_injective h)
    apply (Set.infinite_range_of_injective hinj).mono
    rintro _ ⟨n,rfl⟩
    change Polynomial.eval _ _ = Polynomial.eval _ _
    rw [ray_eval, Polynomial.eval_monomial, hscale (n+1) (Nat.succ_pos n)]
    exact mul_comm _ _
  have h := congrArg (fun Q : Polynomial R => Q.coeff d) heq
  simpa only [ray_coeff, Polynomial.coeff_monomial_same] using h

/-- Integral linear actions commute with scaling a degree vector, after
embedding lattice coordinates into the rationals. -/
theorem lattice_dilate {ι κ : Type*} [Fintype ι]
    (e : (κ → ℤ) ≃ₗ[ℤ] (κ → ℤ)) (c : ι → κ → ℤ) (D : ι → ℕ) (n : ℕ) (j : κ) :
    (e (∑ i, ((n * D i : ℕ) : ℤ) • c i) j : ℚ) =
      (n : ℚ) * (e (∑ i, (D i : ℤ) • c i) j : ℚ) := by
  have h : (∑ i, ((n * D i : ℕ) : ℤ) • c i) =
      (n : ℤ) • ∑ i, (D i : ℤ) • c i := by
    simp only [Nat.cast_mul, Finset.smul_sum, mul_smul]
  rw [h, map_smul]
  simp only [Pi.smul_apply, smul_eq_mul, Int.cast_mul, Int.cast_natCast]

end HomogeneousExtraction

namespace PhilipponMultiplicity.SectionThree
variable {K : Type*} [Field K]

/-- Scaling the block degrees scales the actual Hilbert degree form by the
Hilbert-polynomial dimension. No geometric comparison is needed. -/
theorem locusDegreeValue_scale (M : MultiProjectiveSpace K) (V : Set M.Point)
    (D : M.FactorIndex → ℕ) (n : ℕ) :
    locusDegreeValue M V (fun i => n * D i) =
      (n : ℚ) ^ locusDimension M V * locusDegreeValue M V D := by
  let P := Hilbert.hilbertPolynomial K M.factorCount M.ambientDimension (M.vanishingIdeal V)
  have hhom : (Hilbert.degreeForm K M.factorCount M.ambientDimension
      (M.vanishingIdeal V)).IsHomogeneous P.totalDegree := by
    exact (MvPolynomial.homogeneousSubmodule M.FactorIndex ℚ P.totalDegree).smul_mem _
      (MvPolynomial.homogeneousComponent_mem P.totalDegree P)
  simpa only [locusDegreeValue, idealDegreeValue, Hilbert.degreeValue,
    locusDimension, idealDimension, Nat.cast_mul, P] using
    HomogeneousExtraction.eval_scale _ _ hhom (fun i => (D i : ℚ)) (n : ℚ)

end PhilipponMultiplicity.SectionThree
end

end


section

set_option autoImplicit false
open scoped BigOperators Topology
noncomputable section

namespace PhilipponMultiplicity

theorem homogeneous_degree_of_polynomial_model
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
          (∀ g : G.Point,
            SectionThree.locusDimension G.ambient (Subtype.val '' (τ g '' V)) =
              SectionThree.locusDimension G.ambient (Subtype.val '' V)) ∧
          ∀ (g : G.Point) (D : G.FactorIndex → ℕ), (∀ i, 1 ≤ D i) →
            SectionThree.locusDegreeValue G.ambient (Subtype.val '' (τ g '' V)) D =
              MvPolynomial.eval
                (fun j => (α (Multiplicative.ofAdd (-g)) (∑ i, (D i : ℤ) • c i) j : ℚ)) P) :
    ∃ (m : ℕ)
      (α : Multiplicative G.Point →* ((Fin m → ℤ) ≃ₗ[ℤ] (Fin m → ℤ)))
      (c : G.FactorIndex → (Fin m → ℤ)),
      ∀ (V : Set (groupProjectiveClosure G)),
        @IsClosed _ (TopologicalSpace.induced Subtype.val G.ambient.zariskiTopology) V →
        ∃ P : MvPolynomial (Fin m) ℚ,
          P.IsHomogeneous (SectionThree.locusDimension G.ambient (Subtype.val '' V)) ∧
          ∀ (g : G.Point) (D : G.FactorIndex → ℕ), (∀ i, 1 ≤ D i) →
            SectionThree.locusDegreeValue G.ambient (Subtype.val '' (τ g '' V)) D =
              MvPolynomial.eval
                (fun j => (α (Multiplicative.ofAdd (-g)) (∑ i, (D i : ℤ) • c i) j : ℚ)) P := by
  classical
  obtain ⟨m, α, c, h⟩ := hgeometry
  refine ⟨m, α, c, ?_⟩
  intro V hV
  obtain ⟨P, hdim, hdegree⟩ := h V hV
  refine ⟨MvPolynomial.homogeneousComponent
      (SectionThree.locusDimension G.ambient (Subtype.val '' V)) P,
    MvPolynomial.homogeneousComponent_isHomogeneous _ _, ?_⟩
  intro g D hD
  rw [hdegree g D hD]
  symm
  apply HomogeneousExtraction.component_eval_of_scaling
  intro n hn
  have hnD : ∀ i, 1 ≤ n * D i := fun i =>
    Nat.mul_pos hn (lt_of_lt_of_le Nat.zero_lt_one (hD i))
  calc
    MvPolynomial.eval
        (fun j => (n : ℚ) *
          (α (Multiplicative.ofAdd (-g)) (∑ i, (D i : ℤ) • c i) j : ℚ)) P =
        MvPolynomial.eval
          (fun j => (α (Multiplicative.ofAdd (-g))
            (∑ i, ((n * D i : ℕ) : ℤ) • c i) j : ℚ)) P := by
      congr 2
      funext j
      exact (HomogeneousExtraction.lattice_dilate _ c D n j).symm
    _ = SectionThree.locusDegreeValue G.ambient
        (Subtype.val '' (τ g '' V)) (fun i => n * D i) :=
      (hdegree g (fun i => n * D i) hnD).symm
    _ = _ := by
      rw [SectionThree.locusDegreeValue_scale G.ambient
        (Subtype.val '' (τ g '' V)) D n, hdim g, hdegree g D hD]

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
    ∃ (m : ℕ)
      (α : Multiplicative G.Point →* ((Fin m → ℤ) ≃ₗ[ℤ] (Fin m → ℤ)))
      (c : G.FactorIndex → (Fin m → ℤ)),
      ∀ (V : Set (groupProjectiveClosure G)),
        @IsClosed _ (TopologicalSpace.induced Subtype.val G.ambient.zariskiTopology) V →
        ∃ P : MvPolynomial (Fin m) ℚ,
          P.IsHomogeneous (SectionThree.locusDimension G.ambient (Subtype.val '' V)) ∧
          ∀ (g : G.Point) (D : G.FactorIndex → ℕ), (∀ i, 1 ≤ D i) →
            SectionThree.locusDegreeValue G.ambient (Subtype.val '' (τ g '' V)) D =
              MvPolynomial.eval
                (fun j => (α (Multiplicative.ofAdd (-g)) (∑ i, (D i : ℤ) • c i) j : ℚ)) P := by
  exact homogeneous_degree_of_polynomial_model K hK G τ hzero hadd hregular
    (closure_action_has_dimension_preserving_polynomial_model K hK G τ hzero hadd hregular)
