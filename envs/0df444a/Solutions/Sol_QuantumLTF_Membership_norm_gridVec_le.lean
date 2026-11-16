-- Prove2me | solution 1 for QuantumLTF.Membership.norm_gridVec_le
-- status  : ACCEPTED   (prove)
-- author  : @stockfish-soup
-- created : 2026-11-15T18:54:30.022969+00:00
-- url     : https://prove2.me/submissions/71f3f67b-5571-4d74-911b-aa79368328c8

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Basic
import Definitions.Def_QuantumLTF_Membership_gridVec
import Theorems.Thm_QuantumLTF_Membership_abs_gridPoint_le_half

open QAlgorithms
open QuantumLTF.Membership

theorem solution (n b : ℕ) (x : Fin n → Qubits b) :
    ‖gridVec n b x‖ ≤ Real.sqrt n / 2 := by
  rw [EuclideanSpace.norm_eq, Real.sqrt_le_iff]
  constructor
  · positivity
  · have hsum : ∑ i : Fin n, ‖(gridVec n b x).ofLp i‖ ^ 2 ≤
        ∑ _i : Fin n, (1 / 2 : ℝ) ^ 2 := by
      apply Finset.sum_le_sum
      intro i hi
      have hcoord := abs_gridPoint_le_half b (x i)
      have hnonneg : 0 ≤ |gridPoint b (x i)| := abs_nonneg _
      simp only [gridVec, WithLp.ofLp_toLp, Real.norm_eq_abs]
      nlinarith [sq_nonneg (|gridPoint b (x i)| - 1 / 2)]
    calc
      ∑ i : Fin n, ‖(gridVec n b x).ofLp i‖ ^ 2 ≤
          ∑ _i : Fin n, (1 / 2 : ℝ) ^ 2 := hsum
      _ = (n : ℝ) / 4 := by simp; ring
      _ = (Real.sqrt n / 2) ^ 2 := by
        rw [div_pow, Real.sq_sqrt (by positivity)]
        norm_num
