-- Prove2me | solution 1 for QEC.Distillation.HH18.HH18SublogarithmicEntropy.p0_logA_upper
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T21:29:05.856002+00:00
-- url     : https://prove2.me/submissions/d3427a2e-4d66-446c-82ef-f2c4f3e87f78

import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Sublogarithmic_BinomialTailAsymptotics
import Mathlib.Analysis.SpecialFunctions.BinaryEntropy
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Sublogarithmic_Entropy
import Theorems.Thm_QEC_Distillation_HH18_HH18SublogarithmicEntropy_logOneAdd_le_partial_add_remainder
import Theorems.Thm_QEC_Distillation_HH18_HH18SublogarithmicEntropy_logOneAddPartial_one_eq_s1
import Theorems.Thm_QEC_Distillation_HH18_HH18SublogarithmicEntropy_p0_series_parameters
import Theorems.Thm_QEC_Distillation_HH18_HH18SublogarithmicEntropy_p0_logA_remainder_bound
import Theorems.Thm_QEC_Distillation_HH18_HH18SublogarithmicEntropy_p0_range_reductions

set_option autoImplicit false
open scoped BigOperators
open QEC QEC.Distillation QEC.Distillation.HH18 QEC.Distillation.HH18.HH18SublogarithmicEntropy
open Filter Topology
noncomputable section
namespace QEC.Distillation.HH18.HH18SublogarithmicEntropy
theorem _root_.solution : p0A ≤ logAUpper := by
  have h := logOneAdd_le_partial_add_remainder (a := aA) (N := 1)
    (by norm_num [aA])
  rcases p0_range_reductions with ⟨hA, _, _, _⟩
  rcases p0_series_parameters with ⟨_, hAparam, _, _, _⟩
  have hrem := p0_logA_remainder_bound
  have hrem' : logOneAddRemainder yA 1 ≤ 1 / 23400 := by
    rw [← hAparam]
    exact hrem
  calc
    p0A = Real.log (1 + aA) := hA
    _ ≤ logOneAddPartial aA 1 + logOneAddRemainder (aA / (aA + 2)) 1 := h
    _ = s1 yA + logOneAddRemainder yA 1 := by
      rw [logOneAddPartial_one_eq_s1, hAparam]
    _ ≤ s1 yA + 1 / 23400 := add_le_add_right hrem' _
    _ = logAUpper := rfl
end QEC.Distillation.HH18.HH18SublogarithmicEntropy
