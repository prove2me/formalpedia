-- Prove2me | solution 1 for QuantumWalkSearch.SingularGap.equality_case
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-10-29T02:40:59.654028+00:00
-- url     : https://prove2.me/submissions/f29b19ef-293a-41a2-9e2f-682fe9f87714

import Definitions.Def_QuantumWalkSearch_SingularGap_Discriminant

open Matrix
open QuantumWalkSearch.SingularGap

theorem solution {X : Type*} [Fintype X] [DecidableEq X]
    (P : Matrix X X ℝ) (π : X → ℝ)
    (hP : P ∈ Matrix.rowStochastic ℝ X) (hirr : P.IsIrreducible)
    (hπ : IsStationaryDistribution P π)
    (u w : EuclideanSpace ℂ X) (hu : ‖u‖ = 1) (hw : ‖w‖ = 1)
    (h1 : inner ℂ u (discriminantOp P π w) = 1) :
    ∀ x y : X, 0 < P x y → u x = w y * ((Real.sqrt (π x / π y) : ℝ) : ℂ) := by
  classical
  let U : EuclideanSpace ℂ (X × X) := WithLp.toLp 2 fun p =>
    (Real.sqrt (P p.1 p.2) : ℂ) * u p.1
  let W : EuclideanSpace ℂ (X × X) := WithLp.toLp 2 fun p =>
    ((Real.sqrt (P p.1 p.2) * Real.sqrt (π p.1) / Real.sqrt (π p.2) : ℝ) : ℂ) * w p.2
  have hU : ‖U‖ ^ 2 = 1 := by
    rw [EuclideanSpace.norm_sq_eq, Fintype.sum_prod_type]
    simp only [U, PiLp.toLp_apply, norm_mul, mul_pow]
    simp only [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _),
      Real.sq_sqrt (hP.1 _ _)]
    simp_rw [← Finset.sum_mul, Matrix.sum_row_of_mem_rowStochastic hP, one_mul]
    rw [← EuclideanSpace.norm_sq_eq, hu]
    norm_num
  have hW : ‖W‖ ^ 2 = 1 := by
    rw [EuclideanSpace.norm_sq_eq, Fintype.sum_prod_type]
    calc
      _ = ∑ y, (∑ x, π x * P x y) * (‖w y‖ ^ 2 / π y) := by
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro y hy
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro x hx
        simp only [W, PiLp.toLp_apply, norm_mul, mul_pow, Complex.norm_real,
          Real.norm_eq_abs, abs_div, abs_mul, abs_of_nonneg (Real.sqrt_nonneg _),
          div_pow, Real.sq_sqrt (hP.1 x y), Real.sq_sqrt (hπ.pos x).le,
          Real.sq_sqrt (hπ.pos y).le]
        ring
      _ = ∑ y, ‖w y‖ ^ 2 := by
        apply Finset.sum_congr rfl
        intro y hy
        rw [hπ.stationary y]
        field_simp [ne_of_gt (hπ.pos y)]
      _ = 1 := by rw [← EuclideanSpace.norm_sq_eq, hw]; norm_num
  have hUW : inner ℂ U W = 1 := by
    have heq : inner ℂ U W = inner ℂ u (discriminantOp P π w) := by
      simp only [PiLp.inner_apply, Fintype.sum_prod_type, RCLike.inner_apply',
        U, W, PiLp.toLp_apply, star_mul, Complex.star_def, map_mul, Complex.conj_ofReal,
        discriminantOp, Matrix.toEuclideanLin_apply, Matrix.mulVec, dotProduct,
        discriminant, Matrix.of_apply, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro x hx
      apply Finset.sum_congr rfl
      intro y hy
      have hs : (Real.sqrt (P x y) : ℂ) ^ 2 = (P x y : ℂ) := by
        exact_mod_cast Real.sq_sqrt (hP.1 x y)
      push_cast
      rw [← hs]
      ring
    rw [heq, h1]
  have heq : U = W := by
    have hnorm := @norm_sub_sq ℂ _ _ _ _ U W
    rw [hU, hW, hUW] at hnorm
    norm_num at hnorm
    exact sub_eq_zero.mp hnorm
  intro x y hxy
  have hxy' := congrArg (fun v : EuclideanSpace ℂ (X × X) => v (x, y)) heq
  simp only [U, W, PiLp.toLp_apply] at hxy'
  have hs : 0 < Real.sqrt (P x y) := Real.sqrt_pos.2 hxy
  have hsy : 0 < Real.sqrt (π y) := Real.sqrt_pos.2 (hπ.pos y)
  have hx : Real.sqrt (π x / π y) = Real.sqrt (π x) / Real.sqrt (π y) :=
    Real.sqrt_div (hπ.pos x).le _
  rw [hx]
  push_cast at hxy' ⊢
  have hs' : (Real.sqrt (P x y) : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt hs
  have hsy' : (Real.sqrt (π y) : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt hsy
  field_simp at hxy' ⊢
  linear_combination hxy'
