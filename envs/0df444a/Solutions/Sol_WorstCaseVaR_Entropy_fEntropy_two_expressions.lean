-- Prove2me | solution 1 for WorstCaseVaR.Entropy.fEntropy_two_expressions
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-28T22:44:19.072918+00:00
-- url     : https://prove2.me/submissions/e5964cd5-3f1c-44af-b8ab-c8848d6c914c

import Mathlib
import Definitions.Def_WorstCaseVaR_Entropy_Basic

namespace WorstCaseVaR.Entropy

theorem aux_fE2_image_eq (ε d : ℝ) :
    entropyRatio ε d '' Set.Ioi 0 =
      (fun v : ℝ => (Real.exp (-d) * (v + 1) ^ ε - 1) / v) '' Set.Ioi 0 := by
  ext y
  simp only [Set.mem_image, Set.mem_Ioi]
  constructor
  · rintro ⟨lam, hlam, rfl⟩
    refine ⟨Real.exp (1 / lam) - 1, ?_, ?_⟩
    · have : 1 < Real.exp (1 / lam) := Real.one_lt_exp_iff.mpr (by positivity)
      linarith
    · unfold entropyRatio
      simp only [sub_add_cancel]
      rw [← Real.exp_mul, ← Real.exp_add]
      congr 3
      ring
  · rintro ⟨v, hv, rfl⟩
    have hlog : 0 < Real.log (v + 1) := Real.log_pos (by linarith)
    refine ⟨1 / Real.log (v + 1), by positivity, ?_⟩
    unfold entropyRatio
    have hv1 : 0 < v + 1 := by linarith
    rw [one_div_one_div, Real.exp_log hv1, Real.rpow_def_of_pos hv1, ← Real.exp_add]
    congr 3
    · field_simp
      ring
    · ring

end WorstCaseVaR.Entropy

open WorstCaseVaR.Entropy

theorem solution (ε d : ℝ) :
    fEntropy ε d =
      sSup ((fun v : ℝ => (Real.exp (-d) * (v + 1) ^ ε - 1) / v) '' Set.Ioi 0) := by
  unfold fEntropy
  rw [aux_fE2_image_eq]
