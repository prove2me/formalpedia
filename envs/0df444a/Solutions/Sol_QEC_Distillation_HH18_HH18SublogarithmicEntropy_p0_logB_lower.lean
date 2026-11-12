-- Prove2me | solution 1 for QEC.Distillation.HH18.HH18SublogarithmicEntropy.p0_logB_lower
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T21:26:49.774529+00:00
-- url     : https://prove2.me/submissions/52cc4b1d-10ef-49a8-b5b4-88c659d8fd8a

import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Sublogarithmic_BinomialTailAsymptotics
import Mathlib.Analysis.SpecialFunctions.BinaryEntropy
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Sublogarithmic_Entropy
import Theorems.Thm_QEC_Distillation_HH18_HH18SublogarithmicEntropy_logOneAdd_partial_le
import Theorems.Thm_QEC_Distillation_HH18_HH18SublogarithmicEntropy_logOneAddPartial_three_eq_s3
import Theorems.Thm_QEC_Distillation_HH18_HH18SublogarithmicEntropy_p0_series_parameters
import Theorems.Thm_QEC_Distillation_HH18_HH18SublogarithmicEntropy_p0_range_reductions
import Theorems.Thm_QEC_Distillation_EncodedCode_ImplementsLogicalGate_symm


set_option autoImplicit false
open scoped BigOperators
open QEC QEC.Distillation QEC.Distillation.HH18 QEC.Distillation.HH18.HH18SublogarithmicEntropy
open Filter Topology
noncomputable section
namespace QEC.Distillation.HH18.HH18SublogarithmicEntropy
theorem _root_.solution : logBLower ≤ p0B := by
  have h := logOneAdd_partial_le (a := aB) (N := 3) (by norm_num [aB, p0R, p0Q,
    p0q, HH18ParameterSequence.p0])
  rcases p0_range_reductions with ⟨_, hB, _, _⟩
  rcases p0_series_parameters with ⟨_, _, hBparam, _, _⟩
  calc
    logBLower = s3 yB := rfl
    _ = s3 (aB / (aB + 2)) := by rw [hBparam]
    _ = logOneAddPartial aB 3 := (logOneAddPartial_three_eq_s3 aB).symm
    _ ≤ Real.log (1 + aB) := h
    _ = p0B := hB.symm
end QEC.Distillation.HH18.HH18SublogarithmicEntropy
