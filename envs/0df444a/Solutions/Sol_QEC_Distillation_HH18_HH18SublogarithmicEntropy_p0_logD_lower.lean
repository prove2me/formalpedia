-- Prove2me | solution 1 for QEC.Distillation.HH18.HH18SublogarithmicEntropy.p0_logD_lower
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T21:27:15.241475+00:00
-- url     : https://prove2.me/submissions/c1c25b56-cbe6-4a08-82ba-ac6881cb968c

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
theorem _root_.solution : logDLower ≤ p0D := by
  have h := logOneAdd_partial_le (a := aD) (N := 3) (by norm_num [aD, p0R, p0Q,
    p0u, p0v, HH18ParameterSequence.p0])
  rcases p0_range_reductions with ⟨_, _, _, hD⟩
  rcases p0_series_parameters with ⟨_, _, _, _, hDparam⟩
  calc
    logDLower = s3 yD := rfl
    _ = s3 (aD / (aD + 2)) := by rw [hDparam]
    _ = logOneAddPartial aD 3 := (logOneAddPartial_three_eq_s3 aD).symm
    _ ≤ Real.log (1 + aD) := h
    _ = p0D := hD.symm
end QEC.Distillation.HH18.HH18SublogarithmicEntropy
