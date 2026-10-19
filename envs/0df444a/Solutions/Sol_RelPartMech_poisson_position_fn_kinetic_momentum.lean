-- Prove2me | solution 1 for RelPartMech.poisson_position_fn_kinetic_momentum
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-17T07:35:21.840074+00:00
-- url     : https://prove2.me/submissions/44f6f9f0-9ca8-4d3e-bf0e-ecb84b791ecb

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
theorem solution {n : ℕ} (A : CovectorField n) (e : ℝ)
    (f : Coord n → ℝ) (hf : ContDiff ℝ ∞ f) (β : Fin n) (x p : Coord n) :
    poisson (fun y _ => f y) (kineticMomentum A e β) x p = pd β f x := by
  unfold poisson
  simp only [pdp_const, pdq_const, pdp_kin, zero_mul, sub_zero]
  exact sum_single β _
