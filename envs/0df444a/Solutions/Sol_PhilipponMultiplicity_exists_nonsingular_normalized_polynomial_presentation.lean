-- Prove2me | solution 1 for PhilipponMultiplicity.exists_nonsingular_normalized_polynomial_presentation
-- status  : ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-10-03T10:40:53.178618+00:00
-- url     : https://prove2.me/submissions/74911824-fe08-4ddc-9a81-26607eac261e

import Theorems.Thm_PhilipponMultiplicity_exists_full_rank_normalized_group_equations
import Definitions.Def_PhilipponMultiplicity_Geometry
import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.FDeriv.Pi
import Mathlib.LinearAlgebra.Projection
import Mathlib.Topology.Algebra.Module.FiniteDimension

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open scoped BigOperators

namespace PhilipponMultiplicity.PolynomialJacobian

variable {K σ : Type*} [NontriviallyNormedField K] [Fintype σ]

/-- The formal polynomial gradient, viewed as a continuous linear form. -/
def differential (P : MvPolynomial σ K) (a : σ → K) : (σ → K) →L[K] K :=
  ∑ j, MvPolynomial.eval a (MvPolynomial.pderiv j P) •
    (ContinuousLinearMap.proj j : (σ → K) →L[K] K)

theorem differential_apply (P : MvPolynomial σ K) (a v : σ → K) :
    differential P a v = ∑ j, MvPolynomial.eval a (MvPolynomial.pderiv j P) * v j := by
  simp [differential]

theorem differential_C (b : K) (a : σ → K) :
    differential (MvPolynomial.C b) a = 0 := by
  ext v
  simp [differential_apply]

theorem differential_add (P Q : MvPolynomial σ K) (a : σ → K) :
    differential (P+Q) a = differential P a + differential Q a := by
  ext v
  simp [differential_apply, map_add, add_mul, Finset.sum_add_distrib]

theorem differential_mul (P Q : MvPolynomial σ K) (a : σ → K) :
    differential (P*Q) a = MvPolynomial.eval a P • differential Q a +
      MvPolynomial.eval a Q • differential P a := by
  ext v
  simp only [differential_apply, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.smul_apply, smul_eq_mul, MvPolynomial.pderiv_mul,
    map_add, map_mul, add_mul, Finset.sum_add_distrib, Finset.mul_sum]
  rw [add_comm]
  congr 1 <;> apply Finset.sum_congr rfl <;> intro j hj <;> ring

theorem differential_X (j : σ) (a : σ → K) :
    differential (MvPolynomial.X j) a = ContinuousLinearMap.proj j := by
  classical
  ext v
  simp [differential_apply, MvPolynomial.pderiv_X, Pi.single_apply]

/-- Formal partial derivatives compute the actual Fréchet derivative. -/
theorem hasFDerivAt_eval (P : MvPolynomial σ K) (a : σ → K) :
    HasFDerivAt (fun v : σ → K => MvPolynomial.eval v P) (differential P a) a := by
  induction P using MvPolynomial.induction_on with
  | C b =>
      simpa only [differential_C, MvPolynomial.eval_C] using
        hasFDerivAt_const (𝕜 := K) b a
  | add P Q hP hQ =>
      simpa only [differential_add, map_add, Pi.add_apply] using! hP.add hQ
  | mul_X P j hP =>
      have hX : HasFDerivAt (fun v : σ → K => MvPolynomial.eval v (MvPolynomial.X j))
          (differential (MvPolynomial.X j) a) a := by
        simpa only [differential_X, MvPolynomial.eval_X] using!
          (ContinuousLinearMap.proj (R := K) j).hasFDerivAt (x := a)
      simpa only [differential_mul, map_mul, Pi.mul_apply] using! hP.mul hX

end PhilipponMultiplicity.PolynomialJacobian

end

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 800000

namespace PhilipponMultiplicity.PolynomialJacobian

/-- Complete a surjective finite-dimensional linear map to coordinates by
choosing coordinates on its kernel. -/
theorem exists_complementary_coordinates
    {K σ : Type*} [NontriviallyNormedField K] [CompleteSpace K] [Fintype σ]
    (r : ℕ) (J : (σ → K) →L[K] (Fin r → K)) (hJ : Function.Surjective J) :
    ∃ (d : ℕ) (ρ : (σ → K) →L[K] (Fin d → K))
      (L : (σ → K) ≃L[K] ((Fin r → K) × (Fin d → K))),
      ∀ v, L v = (J v, ρ v) := by
  classical
  let D := J.toLinearMap
  let p := LinearMap.ker D
  obtain ⟨q, hpq⟩ := Submodule.exists_isCompl p
  let π : (σ → K) →ₗ[K] p := p.projectionOnto q hpq
  have hπ : LinearMap.range π = ⊤ := Submodule.range_projectionOnto hpq
  have hker : IsCompl (LinearMap.ker D) (LinearMap.ker π) := by
    simpa only [π, Submodule.ker_projectionOnto] using hpq
  let e₀ := LinearMap.equivProdOfSurjectiveOfIsCompl D π
    (LinearMap.range_eq_top.mpr hJ) hπ hker
  let b := (Module.finBasis K p).equivFun
  let ρ := (b.toLinearMap.comp π).toContinuousLinearMap
  let e := e₀.trans (LinearEquiv.prodCongr (LinearEquiv.refl K (Fin r → K)) b)
  refine ⟨Module.finrank K p, ρ, e.toContinuousLinearEquiv, ?_⟩
  intro v
  rfl

end PhilipponMultiplicity.PolynomialJacobian

end

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators

namespace PhilipponMultiplicity.PolynomialJacobian

/-- A surjective formal Jacobian can be augmented to an invertible analytic
derivative by a continuous linear map to the kernel coordinates. -/
theorem exists_augmented_derivative
    {K σ : Type*} [NontriviallyNormedField K] [CompleteSpace K] [Fintype σ]
    (r : ℕ) (P : Fin r → MvPolynomial σ K) (a : σ → K)
    (hrank : Function.Surjective (fun v : σ → K => fun i : Fin r =>
      ∑ j, MvPolynomial.eval a (MvPolynomial.pderiv j (P i)) * v j)) :
    ∃ (d : ℕ) (ρ : (σ → K) →L[K] (Fin d → K))
      (L : (σ → K) ≃L[K] ((Fin r → K) × (Fin d → K))),
      HasFDerivAt
        (fun v : σ → K => ((fun i => MvPolynomial.eval v (P i)), ρ (v-a)))
        (L : (σ → K) →L[K] ((Fin r → K) × (Fin d → K))) a := by
  let J : (σ → K) →L[K] (Fin r → K) :=
    ContinuousLinearMap.pi (fun i => differential (P i) a)
  have hJ : Function.Surjective J := by
    intro w
    obtain ⟨v, hv⟩ := hrank w
    refine ⟨v, ?_⟩
    funext i
    change differential (P i) a v = w i
    rw [differential_apply]
    exact congrFun hv i
  have hP : HasFDerivAt (fun v : σ → K => fun i => MvPolynomial.eval v (P i)) J a :=
    hasFDerivAt_pi.mpr (fun i => hasFDerivAt_eval (P i) a)
  obtain ⟨d, ρ, L, hL⟩ := exists_complementary_coordinates r J hJ
  have hρ : HasFDerivAt (fun v : σ → K => ρ (v-a)) ρ a := by
    simpa using ρ.hasFDerivAt.comp a ((hasFDerivAt_id a).sub_const a)
  have hLmap : (L : (σ → K) →L[K] ((Fin r → K) × (Fin d → K))) = J.prod ρ := by
    apply ContinuousLinearMap.ext
    intro v
    exact hL v
  refine ⟨d, ρ, L, ?_⟩
  rw [hLmap]
  exact hP.prodMk hρ

end PhilipponMultiplicity.PolynomialJacobian

end

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators

namespace PhilipponMultiplicity.PolynomialJacobian

/-- Reuse the base-field transfers from PhilipponGroupPrimeComponents,
PhilipponPrimeImageReduction and PhilipponCodimensionContainmentReduction. -/
theorem basefield_facts {K : Type*} [NontriviallyNormedField K]
    (hK : IsPhilipponBaseField K) : CompleteSpace K ∧ IsAlgClosed K ∧ CharZero K := by
  have hcomplete : CompleteSpace K := by
    rcases hK with ⟨e, he⟩ | ⟨p, hp, h⟩
    · exact (he.isUniformInducing.completeSpace_congr e.surjective).mpr inferInstance
    · letI : Fact p.Prime := ⟨hp⟩
      obtain ⟨e, he⟩ := h
      exact (he.isUniformInducing.completeSpace_congr e.surjective).mpr inferInstance
  have hchar : CharZero K := by
    rcases hK with ⟨e, _⟩ | ⟨p, hp, h⟩
    · exact e.toRingHom.charZero
    · letI : Fact p.Prime := ⟨hp⟩
      obtain ⟨e, _⟩ := h
      exact e.toRingHom.charZero
  have hclosed : IsAlgClosed K := by
    have transfer (F : Type) [Field F] [IsAlgClosed F] (e : K ≃+* F) : IsAlgClosed K := by
      apply IsAlgClosed.of_exists_root K
      intro P _ hP
      obtain ⟨x, hx⟩ := IsAlgClosed.exists_eval₂_eq_zero e.toRingHom P
        (ne_of_gt (Polynomial.degree_pos_of_irreducible hP))
      refine ⟨e.symm x, ?_⟩
      apply e.injective
      rw [map_zero]
      change e.toRingHom (P.eval (e.symm x)) = 0
      rw [← Polynomial.eval₂_at_apply]
      change P.eval₂ e.toRingHom (e (e.symm x)) = 0
      simpa only [RingEquiv.apply_symm_apply] using hx
    rcases hK with ⟨e, _⟩ | ⟨p, hp, h⟩
    · exact transfer ℂ e
    · letI : Fact p.Prime := ⟨hp⟩
      obtain ⟨e, _⟩ := h
      exact transfer (PadicComplex p) e
  exact ⟨hcomplete, hclosed, hchar⟩

/-- Preserve all geometric equations and construct the analytic Jacobian data. -/
theorem nonsingular_presentation_of_full_rank_equations
    (K : Type*) [NontriviallyNormedField K] [CompleteSpace K]
    (G : EmbeddedGroupProduct K)
    (hgeometry :
    ∃ (r : ℕ)
      (c : ∀ i : G.FactorIndex, Fin ((G.factor i).ambientDimension + 1))
      (a : G.ambient.Variable → K)
      (P : Fin r → G.CoordinateRing) (H : G.CoordinateRing),
      (∀ i, a ⟨i, c i⟩ = 1) ∧
      (∀ i, ∃ h : (fun j => a ⟨i, j⟩) ≠ 0,
        Projectivization.mk K (fun j => a ⟨i, j⟩) h = G.embedding 0 i) ∧
      MvPolynomial.eval a H ≠ 0 ∧
      (∀ i, MvPolynomial.eval a (P i) = 0) ∧
      Function.Surjective (fun v : G.ambient.Variable → K => fun i : Fin r =>
        ∑ j, MvPolynomial.eval a (MvPolynomial.pderiv j (P i)) * v j) ∧
      (∀ v : G.ambient.Variable → K, MvPolynomial.eval v H ≠ 0 →
        ((∀ i, MvPolynomial.eval v (P i) = 0) ↔
          ((∀ i, v ⟨i, c i⟩ = 1) ∧
            ∃ x : G.Point, ∀ i, ∃ h : (fun j => v ⟨i, j⟩) ≠ 0,
              Projectivization.mk K (fun j => v ⟨i, j⟩) h = G.embedding x i)))) :
    ∃ (d r : ℕ)
      (c : ∀ i : G.FactorIndex, Fin ((G.factor i).ambientDimension + 1))
      (a : G.ambient.Variable → K)
      (P : Fin r → G.CoordinateRing) (H : G.CoordinateRing)
      (ρ : (G.ambient.Variable → K) →L[K] (Fin d → K))
      (L : (G.ambient.Variable → K) ≃L[K] ((Fin r → K) × (Fin d → K))),
      (∀ i, a ⟨i, c i⟩ = 1) ∧
      (∀ i, ∃ h : (fun j => a ⟨i, j⟩) ≠ 0,
        Projectivization.mk K (fun j => a ⟨i, j⟩) h = G.embedding 0 i) ∧
      MvPolynomial.eval a H ≠ 0 ∧
      (∀ i, MvPolynomial.eval a (P i) = 0) ∧
      HasFDerivAt
        (fun v : G.ambient.Variable → K =>
          ((fun i => MvPolynomial.eval v (P i)), ρ (v-a)))
        (L : (G.ambient.Variable → K) →L[K] ((Fin r → K) × (Fin d → K))) a ∧
      (∀ v : G.ambient.Variable → K, MvPolynomial.eval v H ≠ 0 →
        ((∀ i, MvPolynomial.eval v (P i) = 0) ↔
          ((∀ i, v ⟨i, c i⟩ = 1) ∧
            ∃ x : G.Point, ∀ i, ∃ h : (fun j => v ⟨i, j⟩) ≠ 0,
              Projectivization.mk K (fun j => v ⟨i, j⟩) h = G.embedding x i))) := by
  obtain ⟨r, c, a, P, H, ha, harep, hH, hP, hrank, hcut⟩ := hgeometry
  obtain ⟨d, ρ, L, hderiv⟩ := exists_augmented_derivative r P a hrank
  exact ⟨d, r, c, a, P, H, ρ, L, ha, harep, hH, hP, hderiv, hcut⟩

end PhilipponMultiplicity.PolynomialJacobian

end

open PhilipponMultiplicity

theorem solution
    (K : Type*) [NontriviallyNormedField K] (hK : IsPhilipponBaseField K)
    (G : EmbeddedGroupProduct K) :
    ∃ (d r : ℕ)
      (c : ∀ i : G.FactorIndex, Fin ((G.factor i).ambientDimension + 1))
      (a : G.ambient.Variable → K)
      (P : Fin r → G.CoordinateRing) (H : G.CoordinateRing)
      (ρ : (G.ambient.Variable → K) →L[K] (Fin d → K))
      (L : (G.ambient.Variable → K) ≃L[K] ((Fin r → K) × (Fin d → K))),
      (∀ i, a ⟨i, c i⟩ = 1) ∧
      (∀ i, ∃ h : (fun j => a ⟨i, j⟩) ≠ 0,
        Projectivization.mk K (fun j => a ⟨i, j⟩) h = G.embedding 0 i) ∧
      MvPolynomial.eval a H ≠ 0 ∧
      (∀ i, MvPolynomial.eval a (P i) = 0) ∧
      HasFDerivAt
        (fun v : G.ambient.Variable → K =>
          ((fun i => MvPolynomial.eval v (P i)), ρ (v-a)))
        (L : (G.ambient.Variable → K) →L[K] ((Fin r → K) × (Fin d → K))) a ∧
      (∀ v : G.ambient.Variable → K, MvPolynomial.eval v H ≠ 0 →
        ((∀ i, MvPolynomial.eval v (P i) = 0) ↔
          ((∀ i, v ⟨i, c i⟩ = 1) ∧
            ∃ x : G.Point, ∀ i, ∃ h : (fun j => v ⟨i, j⟩) ≠ 0,
              Projectivization.mk K (fun j => v ⟨i, j⟩) h = G.embedding x i))) := by
  obtain ⟨hcomplete, hclosed, hchar⟩ := PolynomialJacobian.basefield_facts hK
  letI := hcomplete
  letI := hclosed
  letI := hchar
  exact PolynomialJacobian.nonsingular_presentation_of_full_rank_equations K G
    (exists_full_rank_normalized_group_equations K G)
