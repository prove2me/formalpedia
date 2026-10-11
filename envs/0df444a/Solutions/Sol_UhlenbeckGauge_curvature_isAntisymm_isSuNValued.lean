-- Prove2me | solution 1 for UhlenbeckGauge.curvature_isAntisymm_isSuNValued
-- status  : ACCEPTED   (prove)
-- author  : @SamenHossain
-- created : 2026-10-10T21:31:28.84268+00:00
-- url     : https://prove2.me/submissions/3eb71f77-106b-4b3e-b8f8-ea9e958170bf

import Definitions.Def_uhlenbeck_gauge_box_defs

open UhlenbeckGauge Matrix
open scoped ContDiff
set_option autoImplicit false

namespace UhlenbeckGauge.Sol_curvature

/-- The conjugate transpose of a partial derivative of a smooth skew-Hermitian matrix field is
minus that partial derivative: conjugation is `ℝ`-linear, so it commutes with `∂_μ`. -/
private lemma partialDeriv_conjTranspose {n : ℕ} (μ : Fin 4) (f : R4 → Mat n)
    (hf : ∀ i j, ContDiff ℝ ∞ (fun x => f x i j)) (hskew : ∀ x, (f x)ᴴ = -f x) (x : R4) :
    (partialDeriv μ f x)ᴴ = -partialDeriv μ f x := by
  ext i j
  simp only [partialDeriv, conjTranspose_apply, of_apply]
  rw [neg_apply, of_apply]
  -- entrywise skew-Hermitian: `f y j i = -conj (f y i j)`
  have hji : (fun y => f y j i) = fun y => -(Complex.conjCLE (f y i j)) := by
    funext y
    have h : star (f y j i) = -(f y i j) := by
      have h0 := congrFun (congrFun (hskew y) i) j
      rw [conjTranspose_apply] at h0
      rw [h0]
      rfl
    rw [Complex.conjCLE_apply]
    calc f y j i = star (star (f y j i)) := (star_star _).symm
      _ = star (-(f y i j)) := by rw [h]
      _ = -(starRingEnd ℂ) (f y i j) := by rw [star_neg]; rfl
  have hd : HasFDerivAt (fun y => f y i j) (fderiv ℝ (fun y => f y i j) x) x :=
    ((hf i j).differentiable (by simp) x).hasFDerivAt
  have hd' : HasFDerivAt (fun y => -(Complex.conjCLE (f y i j)))
      (-((Complex.conjCLE : ℂ →L[ℝ] ℂ).comp (fderiv ℝ (fun y => f y i j) x))) x :=
    ((Complex.conjCLE : ℂ →L[ℝ] ℂ).hasFDerivAt.comp x hd).neg
  rw [hji, hd'.fderiv]
  simp

/-- The trace of a partial derivative of a smooth traceless matrix field vanishes. -/
private lemma trace_partialDeriv {n : ℕ} (μ : Fin 4) (f : R4 → Mat n)
    (hf : ∀ i j, ContDiff ℝ ∞ (fun x => f x i j)) (htr : ∀ x, trace (f x) = 0) (x : R4) :
    trace (partialDeriv μ f x) = 0 := by
  have hsum : HasFDerivAt (fun y => ∑ i, f y i i)
      (∑ i, fderiv ℝ (fun y => f y i i) x) x :=
    HasFDerivAt.fun_sum (fun i _ => ((hf i i).differentiable (by simp) x).hasFDerivAt)
  have hzero : (fun y => ∑ i, f y i i) = fun _ => (0 : ℂ) := by
    funext y
    exact htr y
  rw [hzero] at hsum
  have h0 := hsum.unique (hasFDerivAt_const (0 : ℂ) x)
  have := congrArg (fun L : R4 →L[ℝ] ℂ => L (Pi.single μ 1)) h0
  simpa [trace, partialDeriv] using this

/-- `su(n)` is closed under addition, subtraction and commutators. -/
private lemma isSuN_sub {n : ℕ} {X Y : Mat n} (hX : IsSuN X) (hY : IsSuN Y) : IsSuN (X - Y) :=
  ⟨by rw [conjTranspose_sub, hX.1, hY.1]; abel, by rw [trace_sub, hX.2, hY.2, sub_zero]⟩

private lemma isSuN_add {n : ℕ} {X Y : Mat n} (hX : IsSuN X) (hY : IsSuN Y) : IsSuN (X + Y) :=
  ⟨by rw [conjTranspose_add, hX.1, hY.1]; abel, by rw [trace_add, hX.2, hY.2, add_zero]⟩

private lemma isSuN_commutator {n : ℕ} {X Y : Mat n} (hX : IsSuN X) (hY : IsSuN Y) :
    IsSuN (X * Y - Y * X) :=
  ⟨by rw [conjTranspose_sub, conjTranspose_mul, conjTranspose_mul, hX.1, hY.1]
      simp only [neg_mul_neg]
      abel,
   by rw [trace_sub, trace_mul_comm, sub_self]⟩

end UhlenbeckGauge.Sol_curvature

open UhlenbeckGauge.Sol_curvature

/-- The curvature of an `SU(n)`-connection is, at every point, an antisymmetric `su(n)`-valued
two-form: `(F_A)_{νμ} = −(F_A)_{μν}` by the form of `∂_μ A_ν − ∂_ν A_μ + [A_μ, A_ν]`, and each
coefficient is skew-Hermitian and traceless because the partial derivatives of an `su(n)`-valued
smooth field are `su(n)`-valued and `su(n)` is closed under commutators. -/
theorem solution {n : ℕ} (A : Connection n) (hA : IsSUConnection A)
    (x : R4) : IsAntisymm (curvature A x) ∧ IsSuNValued (curvature A x) := by
  refine ⟨fun μ ν => ?_, fun μ ν => ?_⟩
  · simp only [curvature]
    abel
  · have hd : ∀ ρ σ, IsSuN (partialDeriv ρ (fun y => A y σ) x) := fun ρ σ =>
      ⟨partialDeriv_conjTranspose ρ (fun y => A y σ) (hA.1 σ) (fun y => (hA.2 y σ).1) x,
       trace_partialDeriv ρ (fun y => A y σ) (hA.1 σ) (fun y => (hA.2 y σ).2) x⟩
    exact isSuN_add (isSuN_sub (hd μ ν) (hd ν μ)) (isSuN_commutator (hA.2 x μ) (hA.2 x ν))
