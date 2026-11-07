-- Prove2me | solution 1 for QEC.Coding.BDL26RandomPerturbation.exists_cap_integer
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T14:50:38.579206+00:00
-- url     : https://prove2.me/submissions/a00da00e-1240-4416-800c-6f0d48c5be0b

import Definitions.Def_QEC_Coding_ProbabilisticConstruction_SphericalCap_Area
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_Parameters
import Theorems.Thm_QEC_Coding_BDL26RandomPerturbation_widthFactor_pos

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26RandomPerturbation
open QEC.Coding.ProbabilisticConstruction.SphericalCap
namespace QEC.Coding.BDL26RandomPerturbation
theorem _root_.solution : ∃ m : ℕ, 2 ≤ m ∧ 1 < 6 * (m : ℝ) * widthFactor := by
  obtain ⟨m, hm⟩ := exists_nat_gt (max 2 (1 / (6 * widthFactor)))
  have hm2 : (2 : ℝ) < m := lt_of_le_of_lt (le_max_left _ _) hm
  have hmdiv : 1 / (6 * widthFactor) < (m : ℝ) :=
    lt_of_le_of_lt (le_max_right _ _) hm
  have hp : 0 < 6 * widthFactor := mul_pos (by norm_num) widthFactor_pos
  have hmprod := (div_lt_iff₀ hp).mp hmdiv
  refine ⟨m, ?_, ?_⟩
  · exact_mod_cast hm2.le
  · nlinarith
end QEC.Coding.BDL26RandomPerturbation
