-- Prove2me | solution 1 for QEC.Coding.BDL26RandomPerturbation.exists_integer_scale
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T14:50:48.653835+00:00
-- url     : https://prove2.me/submissions/7261836e-a7a1-4052-bc3a-dbbd706a1453

import Definitions.Def_QEC_Coding_ProbabilisticConstruction_SphericalCap_Area
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_Parameters
import Theorems.Thm_QEC_Coding_BDL26RandomPerturbation_perturbationScale_bounds

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26RandomPerturbation
open QEC.Coding.ProbabilisticConstruction.SphericalCap
namespace QEC.Coding.BDL26RandomPerturbation
theorem _root_.solution {alpha probabilityConstant : ℝ} (ha : 0 ≤ alpha) (D : ℕ) :
    ∃ lambda : ℕ, 1 ≤ lambda ∧ 13 ≤ (2*alpha+1)*(lambda : ℝ) ∧
      4*probabilityConstant*(D+1) ≤ (lambda : ℝ) := by
  obtain ⟨lambda,hl⟩ := exists_nat_gt (perturbationScale alpha probabilityConstant D)
  have hb := perturbationScale_bounds (probabilityConstant := probabilityConstant) ha D
  refine ⟨lambda, ?_, ?_, hb.2.2.trans hl.le⟩
  · exact_mod_cast hb.1.trans hl.le
  · exact hb.2.1.trans (mul_le_mul_of_nonneg_left hl.le (by linarith))
end QEC.Coding.BDL26RandomPerturbation
