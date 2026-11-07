-- Prove2me | solution 1 for QEC.Coding.BDL26RandomPerturbation.cap_integer_bounds
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T14:50:43.150203+00:00
-- url     : https://prove2.me/submissions/5898a370-9c30-4339-b4b6-31b1d0b2143d

import Definitions.Def_QEC_Coding_ProbabilisticConstruction_SphericalCap_Area
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_Parameters

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26RandomPerturbation
open QEC.Coding.ProbabilisticConstruction.SphericalCap
namespace QEC.Coding.BDL26RandomPerturbation
theorem _root_.solution {m : ℕ} (hm : 2 ≤ m)
    (hw : 1 < 6 * (m : ℝ) * widthFactor) :
    1 < (m : ℝ) ∧ 1 < 2 * (m : ℝ) ∧ 2 * (m : ℝ) < 6 * m ∧
      0 < 6 * (m : ℝ) * widthFactor - 1 ∧
      0 < 1 / (12 * (m : ℝ)) ∧ 1 / (12 * (m : ℝ)) < Real.pi := by
  have hm' : (2 : ℝ) ≤ m := by exact_mod_cast hm
  have hp : 0 < 12 * (m : ℝ) := by positivity
  have hθ : (1 : ℝ) / (12 * m) ≤ 1 := (div_le_iff₀ hp).mpr (by linarith)
  have hpi := Real.two_le_pi
  refine ⟨by linarith, by linarith, by linarith, by linarith, by positivity, ?_⟩
  linarith
end QEC.Coding.BDL26RandomPerturbation
