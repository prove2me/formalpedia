-- Prove2me | solution 1 for QAlgorithms.Childs.trace_mul_mul_le_frob_spec_frob
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-17T05:12:09.120262+00:00
-- url     : https://prove2.me/submissions/f706bb9d-4b27-49ab-a926-9d8bf1292d84

import Definitions.Def_QAlgorithms_Defs_Basic

set_option autoImplicit false

open Matrix QAlgorithms
open scoped ComplexConjugate

private lemma frob_rows {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℂ) :
    frobNorm A = Real.sqrt (∑ i, ‖(WithLp.toLp 2 (A i) : EuclideanSpace ℂ (Fin n))‖ ^ 2) := by
  unfold frobNorm
  rw [Matrix.frobenius_norm_def, Real.sqrt_eq_rpow]
  simp only [EuclideanSpace.norm_sq_eq, Real.rpow_two]

theorem solution {m n : ℕ} (X : Matrix (Fin m) (Fin n) ℂ)
    (Y : Matrix (Fin n) (Fin n) ℂ) (Z : Matrix (Fin n) (Fin m) ℂ) :
    ‖(X * Y * Z).trace‖ ≤ frobNorm X * specNorm Y * frobNorm Z := by
  let x : Fin m → EuclideanSpace ℂ (Fin n) :=
    fun a => WithLp.toLp 2 (fun b => star (X a b))
  let z : Fin m → EuclideanSpace ℂ (Fin n) :=
    fun a => WithLp.toLp 2 (fun b => Z b a)
  have trace_eq : (X * Y * Z).trace =
      ∑ a, inner ℂ (x a) (act Y (z a)) := by
    rw [Matrix.mul_assoc]
    simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply,
      EuclideanSpace.inner_eq_star_dotProduct, dotProduct, act, x, z,
      Pi.star_apply, star_star, Matrix.mulVec, mul_comm]
  have op_bound (a : Fin m) : ‖act Y (z a)‖ ≤ specNorm Y * ‖z a‖ := by
    exact Matrix.l2_opNorm_mulVec Y (z a)
  have point_bound (a : Fin m) :
      ‖inner ℂ (x a) (act Y (z a))‖ ≤ specNorm Y * (‖x a‖ * ‖z a‖) := by
    calc
      _ ≤ ‖x a‖ * ‖act Y (z a)‖ := norm_inner_le_norm _ _
      _ ≤ ‖x a‖ * (specNorm Y * ‖z a‖) :=
        mul_le_mul_of_nonneg_left (op_bound a) (norm_nonneg _)
      _ = _ := by ring
  have hx : Real.sqrt (∑ a, ‖x a‖ ^ 2) = frobNorm X := by
    rw [frob_rows]
    simp only [x, EuclideanSpace.norm_sq_eq, norm_star]
  have hz : Real.sqrt (∑ a, ‖z a‖ ^ 2) = frobNorm Z := by
    rw [frob_rows]
    simp only [z, EuclideanSpace.norm_sq_eq]
    congr 1
    exact Finset.sum_comm
  have hspec : 0 ≤ specNorm Y := by
    letI := Matrix.instL2OpNormedAddCommGroup (𝕜 := ℂ) (m := Fin n) (n := Fin n)
    exact norm_nonneg Y
  calc
    ‖(X * Y * Z).trace‖ = ‖∑ a, inner ℂ (x a) (act Y (z a))‖ := by rw [trace_eq]
    _ ≤ ∑ a, ‖inner ℂ (x a) (act Y (z a))‖ := norm_sum_le _ _
    _ ≤ ∑ a, specNorm Y * (‖x a‖ * ‖z a‖) := Finset.sum_le_sum fun a _ => point_bound a
    _ = specNorm Y * (∑ a, ‖x a‖ * ‖z a‖) := (Finset.mul_sum _ _ _).symm
    _ ≤ specNorm Y * (Real.sqrt (∑ a, ‖x a‖ ^ 2) *
        Real.sqrt (∑ a, ‖z a‖ ^ 2)) := by
      apply mul_le_mul_of_nonneg_left _ hspec
      simpa using
        Real.sum_mul_le_sqrt_mul_sqrt Finset.univ (fun a => ‖x a‖) (fun a => ‖z a‖)
    _ = frobNorm X * specNorm Y * frobNorm Z := by rw [hx, hz]; ring
