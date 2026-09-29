-- Prove2me | solution 1 for SparseApprox.Greedy.opNorm2_pinv_submatrix_le
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-29T01:50:07.560249+00:00
-- url     : https://prove2.me/submissions/545b245a-56b8-410f-83e5-f5f04133cab4

import Mathlib
import Definitions.Def_SparseApprox_Greedy_Basic
import Definitions.Def_SparseApprox_Greedy_Algorithm

open scoped InnerProductSpace

namespace SparseApprox.Greedy

open scoped Matrix.Norms.L2Operator

theorem aux_opnps_PM_eq_one {m n : ℕ} (M : Matrix (Fin m) (Fin n) ℝ)
    (hM : LinearIndependent ℝ (colE M))
    (P : Matrix (Fin n) (Fin m) ℝ) (hP : IsMoorePenrose M P) :
    P * M = 1 := by
  have hX : M * (P * M - 1) = 0 := by
    rw [Matrix.mul_sub, ← Matrix.mul_assoc, hP.1, Matrix.mul_one, sub_self]
  rw [Fintype.linearIndependent_iff] at hM
  ext k j
  have h := hM (fun k => (P * M - 1 : Matrix (Fin n) (Fin n) ℝ) k j) (by
    ext a
    have := congrFun (congrFun hX a) j
    simp only [Matrix.mul_apply, Matrix.zero_apply] at this
    simp only [colE, PiLp.zero_apply]
    rw [WithLp.ofLp_sum]
    simp only [Finset.sum_apply, WithLp.ofLp_smul, Pi.smul_apply, smul_eq_mul]
    rw [← this]
    refine Finset.sum_congr rfl fun x _ => ?_
    ring) k
  have := sub_eq_zero.mp (show (P * M - 1 : Matrix (Fin n) (Fin n) ℝ) k j = 0 from h)
  simpa [Matrix.sub_apply] using this

theorem aux_opnps_norm_le_one_of_proj {m : ℕ} (Q : Matrix (Fin m) (Fin m) ℝ)
    (hs : Q.transpose = Q) (hi : Q * Q = Q) : ‖Q‖ ≤ 1 := by
  have h := Matrix.l2_opNorm_conjTranspose_mul_self Q
  rw [Matrix.conjTranspose_eq_transpose_of_trivial, hs, hi] at h
  have h0 : 0 ≤ ‖Q‖ := norm_nonneg _
  nlinarith

end SparseApprox.Greedy

open SparseApprox.Greedy
open scoped InnerProductSpace
open scoped Matrix.Norms.L2Operator

theorem solution {m n : ℕ} (M : Matrix (Fin m) (Fin n) ℝ)
    (hM : LinearIndependent ℝ (colE M))
    (P : Matrix (Fin n) (Fin m) ℝ) (hP : IsMoorePenrose M P)
    (S : Finset (Fin n)) (PS : Matrix ↥S (Fin m) ℝ)
    (hPS : IsMoorePenrose (colsMatrix (fun i : ↥S => colE M i)) PS) :
    opNorm2 PS ≤ opNorm2 P := by
  set Z := colsMatrix (fun i : ↥S => colE M i) with hZdef
  let E : Matrix (Fin n) ↥S ℝ := Matrix.of fun j i => if j = i.val then 1 else 0
  have hZ : Z = M * E := by
    ext a i
    simp [hZdef, colsMatrix, colE, E, Matrix.mul_apply]
  have hEE : E.transpose * E = 1 := by
    ext i i'
    simp only [E, Matrix.mul_apply, Matrix.transpose_apply, Matrix.of_apply, Matrix.one_apply]
    by_cases h : i = i'
    · subst h; simp
    · have : (i : Fin n) ≠ i' := fun h' => h (Subtype.ext h')
      simp [h]
      intro x
      exact h x.symm
  have hPM := aux_opnps_PM_eq_one M hM P hP
  have hEPZ : E.transpose * P * Z = 1 := by
    rw [hZ, Matrix.mul_assoc, ← Matrix.mul_assoc P, hPM, Matrix.one_mul, hEE]
  have hPSeq : PS = E.transpose * P * (Z * PS) := by
    rw [← Matrix.mul_assoc, hEPZ, Matrix.one_mul]
  have hQ : ‖Z * PS‖ ≤ 1 :=
    aux_opnps_norm_le_one_of_proj _ hPS.2.2.1 (by rw [← Matrix.mul_assoc, hPS.1])
  have hE : ‖E.transpose‖ ≤ 1 := by
    have h := Matrix.l2_opNorm_conjTranspose_mul_self E
    rw [Matrix.conjTranspose_eq_transpose_of_trivial, hEE] at h
    have h1 : ‖(1 : Matrix ↥S ↥S ℝ)‖ ≤ 1 := by
      rw [← Matrix.l2_opNorm_toEuclideanCLM, map_one]
      exact ContinuousLinearMap.norm_id_le
    rw [← Matrix.conjTranspose_eq_transpose_of_trivial, Matrix.l2_opNorm_conjTranspose]
    nlinarith [norm_nonneg E]
  show ‖PS‖ ≤ ‖P‖
  rw [hPSeq]
  have h0 : ‖E.transpose * P * (Z * PS)‖ ≤ ‖E.transpose * P‖ * ‖Z * PS‖ :=
    Matrix.l2_opNorm_mul _ _
  have h0' : ‖E.transpose * P‖ ≤ ‖E.transpose‖ * ‖P‖ := Matrix.l2_opNorm_mul _ _
  have h1 : ‖E.transpose‖ * ‖P‖ ≤ ‖P‖ := mul_le_of_le_one_left (norm_nonneg _) hE
  have h2 : ‖E.transpose * P‖ * ‖Z * PS‖ ≤ ‖E.transpose * P‖ :=
    mul_le_of_le_one_right (norm_nonneg _) hQ
  linarith
