-- Prove2me | solution 1 for QEC.Distillation.HH18.HH18SublogarithmicEntropy.p0_log_four
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T21:29:15.303766+00:00
-- url     : https://prove2.me/submissions/7742e311-770c-4736-b31a-5ff9438dfb72

import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Sublogarithmic_BinomialTailAsymptotics
import Mathlib.Analysis.SpecialFunctions.BinaryEntropy
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Sublogarithmic_Entropy

set_option autoImplicit false
open scoped BigOperators
open QEC QEC.Distillation QEC.Distillation.HH18 QEC.Distillation.HH18.HH18SublogarithmicEntropy
open Filter Topology
noncomputable section
namespace QEC.Distillation.HH18.HH18SublogarithmicEntropy
theorem _root_.solution : Real.log (4 : ℝ) = 2 * Real.log 2 := by
  calc
    Real.log (4 : ℝ) = Real.log ((2 : ℝ) ^ 2) := by norm_num
    _ = 2 * Real.log 2 := by
      rw [Real.log_pow]
      norm_num
end QEC.Distillation.HH18.HH18SublogarithmicEntropy
