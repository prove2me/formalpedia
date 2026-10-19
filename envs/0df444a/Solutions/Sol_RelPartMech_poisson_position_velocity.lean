-- Prove2me | solution 1 for RelPartMech.poisson_position_velocity
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-17T07:37:50.832767+00:00
-- url     : https://prove2.me/submissions/5bdc7b76-472e-4eaa-986f-f68643dedd1f

import Mathlib
import Definitions.Def_RelPartMech_coordinates
open scoped ContDiff
open RelPartMech

namespace RPAux

lemma pdp_const {n : ℕ} (f : Coord n → ℝ) (μ : Fin n) (x p : Coord n) :
    pdp μ (fun y _ => f y) x p = 0 := by
  simp [pdp]

lemma pdq_const {n : ℕ} (f : Coord n → ℝ) (μ : Fin n) (x p : Coord n) :
    pdq μ (fun y _ => f y) x p = pd μ f x := rfl

lemma pdp_kin {n : ℕ} (A : CovectorField n) (e : ℝ) (β μ : Fin n) (x p : Coord n) :
    pdp μ (kineticMomentum A e β) x p = (Pi.single μ (1:ℝ) : Coord n) β := by
  unfold pdp kineticMomentum
  have h : HasFDerivAt (fun r : Coord n => r β - e * A β x) (ContinuousLinearMap.proj β) p :=
    (hasFDerivAt_apply (𝕜 := ℝ) (F' := fun _ : Fin n => ℝ) β p).sub_const (e * A β x)
  rw [h.fderiv]; rfl

lemma pdq_kin {n : ℕ} (A : CovectorField n) (e : ℝ) (β μ : Fin n) (x p : Coord n)
    (hA : DifferentiableAt ℝ (A β) x) :
    pdq μ (kineticMomentum A e β) x p = -(e * pd μ (A β) x) := by
  unfold pdq kineticMomentum pd
  have h : HasFDerivAt (fun y : Coord n => p β - e * A β y) (-(e • fderiv ℝ (A β) x)) x := by
    have := (hA.hasFDerivAt.const_mul e).const_sub (p β)
    simpa using this
  rw [h.fderiv]; simp

lemma pdq_pos {n : ℕ} (α μ : Fin n) (x p : Coord n) :
    pdq μ (posFn α) x p = (Pi.single μ (1:ℝ) : Coord n) α := by
  unfold pdq posFn
  rw [(hasFDerivAt_apply (𝕜 := ℝ) (F' := fun _ : Fin n => ℝ) α x).fderiv]; rfl

lemma pdp_pos {n : ℕ} (α μ : Fin n) (x p : Coord n) :
    pdp μ (posFn α) x p = 0 := by
  simp [pdp, posFn]

lemma sum_single {n : ℕ} (β : Fin n) (c : Fin n → ℝ) :
    ∑ μ, c μ * (Pi.single μ (1:ℝ) : Coord n) β = c β := by
  simp [Pi.single_apply]

end RPAux

namespace RPAux

lemma ginv_symm {n : ℕ} (g : MetricField n) (hg : IsSmoothMetric g) (x : Coord n) (i j : Fin n) :
    ginv g x i j = ginv g x j i := by
  have ht : Matrix.transpose (g x) = g x := by ext a b; exact hg.2.1 x b a
  have : Matrix.transpose (ginv g x) = ginv g x := by
    unfold ginv; rw [Matrix.transpose_nonsing_inv, ht]
  have h := congrFun (congrFun this j) i
  rw [Matrix.transpose_apply] at h
  exact h

lemma hasFDeriv_kin_p {n : ℕ} (A : CovectorField n) (e : ℝ) (β : Fin n) (x p : Coord n) :
    HasFDerivAt (fun r => kineticMomentum A e β x r) (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin n => ℝ) β) p :=
  (hasFDerivAt_apply (𝕜 := ℝ) (F' := fun _ : Fin n => ℝ) β p).sub_const (e * A β x)

lemma pdp_ham {n : ℕ} (g : MetricField n) (hg : IsSmoothMetric g) (A : CovectorField n)
    (e m : ℝ) (α : Fin n) (x p : Coord n) :
    pdp α (hamiltonian g A e m) x p = (1 / m) * ∑ β, ginv g x α β * kineticMomentum A e β x p := by
  unfold pdp hamiltonian
  have hK := fun β => hasFDeriv_kin_p A e β x p
  have h : HasFDerivAt (fun r => 1 / (2 * m) * ∑ β, ∑ γ,
      kineticMomentum A e β x r * ginv g x β γ * kineticMomentum A e γ x r) _ p := (HasFDerivAt.fun_sum (u := Finset.univ) (fun β _ => HasFDerivAt.fun_sum (u := Finset.univ)
    (fun γ _ => ((hK β).mul_const (ginv g x β γ)).mul (hK γ)))).const_mul (1 / (2 * m))
  rw [h.fderiv]
  simp only [ContinuousLinearMap.coe_smul', ContinuousLinearMap.coe_sum', ContinuousLinearMap.add_apply, Pi.smul_apply, Finset.sum_apply,
    smul_eq_mul, ContinuousLinearMap.proj_apply]
  simp only [Pi.single_apply, mul_ite, mul_one, mul_zero, ite_mul, zero_mul, one_mul, Finset.sum_add_distrib,
    Finset.sum_ite_eq', Finset.sum_ite_eq, Finset.mem_univ, if_true]
  rw [Finset.sum_comm (f := fun x_1 x_2 => if x_1 = α then kineticMomentum A e x_2 x p * ginv g x x_1 x_2 else 0)]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true]
  have : ∀ β, kineticMomentum A e β x p * ginv g x β α = ginv g x α β * kineticMomentum A e β x p := by
    intro β; rw [ginv_symm g hg x β α]; ring
  simp only [this]
  have e2 : ∀ β, kineticMomentum A e β x p * ginv g x α β = ginv g x α β * kineticMomentum A e β x p :=
    fun β => mul_comm _ _
  simp only [e2]
  by_cases hm : m = 0
  · simp [hm]
  · field_simp; ring

end RPAux

namespace RPAux

lemma poisson_pos {n : ℕ} (α : Fin n) (h : PhaseFn n) (x p : Coord n) :
    poisson (posFn α) h x p = pdp α h x p := by
  unfold poisson
  simp only [pdq_pos, pdp_pos, zero_mul, sub_zero]
  rw [← sum_single α (fun μ => pdp μ h x p)]
  exact Finset.sum_congr rfl (fun _ _ => mul_comm _ _)

lemma pdp_vel {n : ℕ} (g : MetricField n) (hg : IsSmoothMetric g) (A : CovectorField n)
    (e m : ℝ) (α β : Fin n) (x p : Coord n) :
    pdp α (velocity g A e m β) x p = (1 / m) * ginv g x α β := by
  unfold pdp velocity
  have hK := fun β => hasFDeriv_kin_p A e β x p
  have h : HasFDerivAt (fun r => (1 / m) * ∑ γ, ginv g x β γ * kineticMomentum A e γ x r) _ p :=
    (HasFDerivAt.fun_sum (u := Finset.univ) (fun γ _ => (hK γ).const_mul (ginv g x β γ))).const_mul (1 / m)
  rw [h.fderiv]
  simp [Pi.single_apply, ginv_symm g hg x β α]

end RPAux

open RPAux in
theorem solution {n : ℕ} (g : MetricField n) (hg : IsSmoothMetric g)
    (A : CovectorField n) (hA : ∀ α, ContDiff ℝ ∞ (A α)) (e m : ℝ) (hm : m ≠ 0)
    (α β : Fin n) (x p : Coord n) :
    poisson (posFn α) (velocity g A e m β) x p = (1 / m) * ginv g x α β := by
  rw [poisson_pos, pdp_vel g hg]
