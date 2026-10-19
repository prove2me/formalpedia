-- Prove2me | solution 1 for QAlgorithms.DeWolf.binEntropy2_gap_quadratic
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-18T02:48:13.39113+00:00
-- url     : https://prove2.me/submissions/4b38a51a-5f3f-4f9f-b427-5ac817c3529d

import Definitions.Def_QAlgorithms_Defs_Information
import Mathlib.Analysis.SpecialFunctions.BinaryEntropy
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Tactic

open QAlgorithms

theorem solution (η : ℝ) (hη : 0 ≤ η) (hη1 : η ≤ 1 / 2) :
    η ^ 2 ≤ 1 - binEntropy2 (1 / 2 + η) := by
  let f : ℝ → ℝ := fun p => Real.log 2 - Real.binEntropy p - (p - 1 / 2) ^ 2
  have hm : MonotoneOn f (Set.Icc (1 / 2) 1) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc _ _)
    · exact ((continuous_const.sub Real.binEntropy_continuous).sub (by fun_prop)).continuousOn
    · intro p hp
      simp only [interior_Icc, Set.mem_Ioo] at hp
      have hp0 : 0 < p := by linarith
      have hpne : p ≠ 1 := by linarith
      exact (((hasDerivAt_const p (Real.log 2)).sub
        (Real.hasDerivAt_binEntropy hp0.ne' hpne)).sub
          (((hasDerivAt_id p).sub_const (1 / 2)).pow 2)).differentiableAt.differentiableWithinAt
    · intro p hp
      simp only [interior_Icc, Set.mem_Ioo] at hp
      have hp0 : 0 < p := by linarith
      have hp1 : 0 < 1 - p := by linarith
      have hd : HasDerivAt f
          (-(Real.log (1 - p) - Real.log p) - 2 * (p - 1 / 2)) p := by
        convert (((hasDerivAt_const p (Real.log 2)).sub
          (Real.hasDerivAt_binEntropy hp0.ne' (by linarith))).sub
            (((hasDerivAt_id p).sub_const (1 / 2)).pow 2)) using 1 <;>
          first | rfl | norm_num [f, Pi.sub_apply, Pi.pow_apply]
      change 0 ≤ deriv f p
      rw [hd.deriv]
      have hl := Real.log_le_sub_one_of_pos (div_pos hp1 hp0)
      rw [Real.log_div hp1.ne' hp0.ne'] at hl
      have hb : (1 - p) / p - 1 ≤ -(2 * (p - 1 / 2)) := by
        apply (sub_le_iff_le_add).2
        apply (div_le_iff₀ hp0).2
        nlinarith [mul_nonpos_of_nonneg_of_nonpos
          (show 0 ≤ 2 * p - 1 by linarith) (show p - 1 ≤ 0 by linarith)]
      nlinarith
  have hx : (1 / 2 + η : ℝ) ∈ Set.Icc (1 / 2) 1 := by constructor <;> linarith
  have hg := hm (by norm_num : (1 / 2 : ℝ) ∈ Set.Icc (1 / 2) 1) hx (by linarith)
  have hh : Real.binEntropy (1 / 2) = Real.log 2 := by
    simpa using Real.binEntropy_two_inv
  dsimp [f] at hg
  rw [hh] at hg
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlog1 : Real.log 2 ≤ 1 := by convert Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2) using 1 <;> norm_num
  have hgap : η ^ 2 ≤ Real.log 2 - Real.binEntropy (1 / 2 + η) := by nlinarith [hg]
  unfold binEntropy2
  have hf : η ^ 2 * Real.log 2 ≤ Real.log 2 - Real.binEntropy (1 / 2 + η) :=
    (mul_le_of_le_one_right (sq_nonneg η) hlog1).trans hgap
  rw [le_sub_iff_add_le, add_comm, ← le_sub_iff_add_le]
  apply (div_le_iff₀ hlog).2
  nlinarith [hf]

