-- Prove2me | solution 1 for QEC.Distillation.HH18.HH18SublogarithmicEntropy.p0_inverse_log_reductions
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T21:32:18.285205+00:00
-- url     : https://prove2.me/submissions/4d1cf32f-2b10-40f6-a9c1-3f2ba73a550c

import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Sublogarithmic_BinomialTailAsymptotics
import Mathlib.Analysis.SpecialFunctions.BinaryEntropy
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Sublogarithmic_Entropy
import Theorems.Thm_QEC_Distillation_HH18_HH18SublogarithmicEntropy_p0_interval
import Theorems.Thm_QEC_Distillation_HH18_HH18SublogarithmicEntropy_p0_complements
import Theorems.Thm_QEC_Distillation_HH18_HH18SublogarithmicEntropy_p0_log_four

set_option autoImplicit false
open scoped BigOperators
open QEC QEC.Distillation QEC.Distillation.HH18 QEC.Distillation.HH18.HH18SublogarithmicEntropy
open Filter Topology
noncomputable section
namespace QEC.Distillation.HH18.HH18SublogarithmicEntropy
theorem _root_.solution :
    Real.log (1 / p0R) = 2 * Real.log 2 - p0A ∧
      Real.log (1 / p0q) = p0B ∧
      Real.log (1 / p0u) = p0C ∧
      Real.log (1 / p0v) = 2 * Real.log 2 + p0D := by
  have hp0R_pos : 0 < p0R := (by norm_num : (0 : ℝ) < 1 / 6).trans p0_interval.1
  rcases p0_complements with ⟨_, _, _, _, _, hp0v_pos, _⟩
  constructor
  · calc
      Real.log (1 / p0R) = Real.log (4 / (4 * p0R)) := by
        congr 1
        field_simp [p0R, p0Q, HH18ParameterSequence.p0]
      _ = Real.log 4 - Real.log (4 * p0R) := by
        rw [Real.log_div (by norm_num) (by positivity)]
      _ = 2 * Real.log 2 - p0A := by
        rw [p0_log_four]
        rfl
  constructor
  · rfl
  constructor
  · rfl
  · calc
      Real.log (1 / p0v) = Real.log (4 * (1 / (4 * p0v))) := by
        congr 1
        field_simp [p0R, p0Q, p0u, p0v, HH18ParameterSequence.p0]
      _ = Real.log 4 + Real.log (1 / (4 * p0v)) := by
        rw [Real.log_mul (by norm_num) (by positivity)]
      _ = 2 * Real.log 2 + p0D := by
        rw [p0_log_four]
        rfl
end QEC.Distillation.HH18.HH18SublogarithmicEntropy
