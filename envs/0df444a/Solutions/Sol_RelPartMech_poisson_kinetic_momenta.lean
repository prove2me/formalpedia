-- Prove2me | solution 1 for RelPartMech.poisson_kinetic_momenta
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-17T07:35:29.070742+00:00
-- url     : https://prove2.me/submissions/9a40bbe1-3ced-488d-b929-5382c7fd9f29

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

open RPAux in
theorem solution {n : ℕ} (A : CovectorField n) (hA : ∀ α, ContDiff ℝ ∞ (A α))
    (e : ℝ) (α β : Fin n) (x p : Coord n) :
    poisson (kineticMomentum A e α) (kineticMomentum A e β) x p = e * forceTensor A α β x := by
  have hd : ∀ γ, DifferentiableAt ℝ (A γ) x := fun γ => ((hA γ).differentiable (by simp)) x
  unfold poisson forceTensor
  simp only [pdp_kin, pdq_kin A e _ _ x p (hd _), Finset.sum_sub_distrib]
  rw [sum_single β (fun μ => -(e * pd μ (A α) x))]
  have : ∑ μ, (Pi.single μ (1:ℝ) : Coord n) α * -(e * pd μ (A β) x) = -(e * pd α (A β) x) := by
    rw [← sum_single α (fun μ => -(e * pd μ (A β) x))]
    exact Finset.sum_congr rfl (fun _ _ => mul_comm _ _)
  rw [this]; ring
