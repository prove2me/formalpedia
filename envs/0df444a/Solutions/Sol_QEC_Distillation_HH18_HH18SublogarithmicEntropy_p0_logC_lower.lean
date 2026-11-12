-- Prove2me | solution 1 for QEC.Distillation.HH18.HH18SublogarithmicEntropy.p0_logC_lower
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T21:27:05.559935+00:00
-- url     : https://prove2.me/submissions/a2c2d753-e944-475c-a864-f2582b973711

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
theorem _root_.solution : logCLower ≤ p0C := by
  have h := logOneAdd_partial_le (a := aC) (N := 3) (by norm_num [aC, p0R, p0Q,
    p0u, p0v, HH18ParameterSequence.p0])
  rcases p0_range_reductions with ⟨_, _, hC, _⟩
  rcases p0_series_parameters with ⟨_, _, _, hCparam, _⟩
  calc
    logCLower = s3 yC := rfl
    _ = s3 (aC / (aC + 2)) := by rw [hCparam]
    _ = logOneAddPartial aC 3 := (logOneAddPartial_three_eq_s3 aC).symm
    _ ≤ Real.log (1 + aC) := h
    _ = p0C := hC.symm
end QEC.Distillation.HH18.HH18SublogarithmicEntropy
