-- Prove2me | solution 1 for SatiaLave.MaxMin.eq5_presentValue_unique
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-29T00:00:20.312954+00:00
-- url     : https://prove2.me/submissions/e3c8a71f-4f12-40c3-892e-aafe703d5bbd

import Mathlib
import Definitions.Def_SatiaLave_MaxMin_Model

namespace SatiaLave.MaxMin

open Finset

theorem aux_eq5u_row {S : Type*} [Fintype S] [DecidableEq S] {D : S → Type*}
    (M : UncertainMDP S D) (A : Policy S D) (P : Sel M) (i : S) :
    (∀ j, 0 ≤ P.1 i (A i) j) ∧ ∑ j, P.1 i (A i) j = 1 :=
  M.U_subset i (A i) (P.2 i (A i))

theorem aux_eq5u_det {S : Type*} [Fintype S] [DecidableEq S] {D : S → Type*}
    (M : UncertainMDP S D) (A : Policy S D) (P : Sel M) :
    (1 - M.β • transMat M A P).det ≠ 0 := by
  apply det_ne_zero_of_sum_row_lt_diag
  intro k
  obtain ⟨hnn, hsum⟩ := aux_eq5u_row M A P k
  have hβ0 := M.β_nonneg
  have hβ1 := M.β_lt_one
  have hkk : P.1 k (A k) k ≤ 1 := by
    rw [← hsum]; exact Finset.single_le_sum (fun j _ => hnn j) (Finset.mem_univ k)
  have hoff : ∀ j ∈ Finset.univ.erase k,
      ‖(1 - M.β • transMat M A P) k j‖ = M.β * P.1 k (A k) j := by
    intro j hj
    have hjk : k ≠ j := (Finset.ne_of_mem_erase hj).symm
    rw [Matrix.sub_apply, Matrix.one_apply_ne hjk, Matrix.smul_apply, smul_eq_mul, transMat,
      Matrix.of_apply, zero_sub, norm_neg, Real.norm_eq_abs,
      abs_of_nonneg (mul_nonneg hβ0 (hnn j))]
  have hdiag : ‖(1 - M.β • transMat M A P) k k‖ = 1 - M.β * P.1 k (A k) k := by
    have : M.β * P.1 k (A k) k ≤ M.β := by nlinarith [hnn k]
    rw [Matrix.sub_apply, Matrix.one_apply_eq, Matrix.smul_apply, smul_eq_mul, transMat,
      Matrix.of_apply, Real.norm_eq_abs, abs_of_nonneg (by linarith)]
  rw [Finset.sum_congr rfl hoff, hdiag, ← Finset.mul_sum,
    Finset.sum_erase_eq_sub (Finset.mem_univ k), hsum]
  nlinarith

theorem aux_eq5u_iff {S : Type*} [Fintype S] [DecidableEq S] {D : S → Type*}
    (M : UncertainMDP S D) (A : Policy S D) (P : Sel M) (v : S → ℝ) :
    SolvesEq5 M A P v ↔ (1 - M.β • transMat M A P).mulVec v = rewardVec M A P := by
  have key : ∀ i, ((1 - M.β • transMat M A P).mulVec v) i
      = v i - M.β * ∑ j, P.1 i (A i) j * v j := by
    intro i
    rw [Matrix.sub_mulVec, Matrix.one_mulVec, Matrix.smul_mulVec, Pi.sub_apply, Pi.smul_apply,
      smul_eq_mul]
    rfl
  have key2 : ∀ i, ∑ j, P.1 i (A i) j * (M.r i (A i) j + M.β * v j)
      = rewardVec M A P i + M.β * ∑ j, P.1 i (A i) j * v j := by
    intro i
    simp only [rewardVec, mul_add, Finset.sum_add_distrib, Finset.mul_sum]
    congr 1
    exact Finset.sum_congr rfl fun j _ => by ring
  constructor
  · intro h
    funext i
    have := h i
    rw [key2] at this
    rw [key]
    linarith
  · intro h i
    have := congrFun h i
    rw [key] at this
    rw [key2]
    linarith

end SatiaLave.MaxMin

open SatiaLave.MaxMin

theorem solution {S : Type*} [Fintype S] [DecidableEq S] {D : S → Type*}
    (M : UncertainMDP S D) (A : Policy S D) (P : Sel M) :
    SolvesEq5 M A P (presentValue M A P) ∧
      ∀ v : S → ℝ, SolvesEq5 M A P v → v = presentValue M A P := by
  have hdet := aux_eq5u_det M A P
  have hu : IsUnit (1 - M.β • transMat M A P).det := isUnit_iff_ne_zero.mpr hdet
  refine ⟨?_, ?_⟩
  · rw [aux_eq5u_iff, presentValue, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hu,
      Matrix.one_mulVec]
  · intro v hv
    rw [aux_eq5u_iff] at hv
    rw [presentValue, ← hv, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hu,
      Matrix.one_mulVec]
