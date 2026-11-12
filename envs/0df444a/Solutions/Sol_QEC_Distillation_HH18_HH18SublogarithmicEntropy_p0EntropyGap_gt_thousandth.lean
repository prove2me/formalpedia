-- Prove2me | solution 1 for QEC.Distillation.HH18.HH18SublogarithmicEntropy.p0EntropyGap_gt_thousandth
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T21:40:13.741518+00:00
-- url     : https://prove2.me/submissions/3f3a3980-5b80-4175-ab9b-ab3742bb4ba9

import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Sublogarithmic_BinomialTailAsymptotics
import Mathlib.Analysis.SpecialFunctions.BinaryEntropy
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Sublogarithmic_Entropy
import Theorems.Thm_QEC_Distillation_HH18_HH18SublogarithmicEntropy_p0_log2_upper
import Theorems.Thm_QEC_Distillation_HH18_HH18SublogarithmicEntropy_p0_logA_upper
import Theorems.Thm_QEC_Distillation_HH18_HH18SublogarithmicEntropy_p0_logB_lower
import Theorems.Thm_QEC_Distillation_HH18_HH18SublogarithmicEntropy_p0_logC_lower
import Theorems.Thm_QEC_Distillation_HH18_HH18SublogarithmicEntropy_p0_logD_lower
import Theorems.Thm_QEC_Distillation_HH18_HH18SublogarithmicEntropy_p0CertifiedGapQ_gt_thousandth
import Theorems.Thm_QEC_Distillation_HH18_HH18SublogarithmicEntropy_p0LinearLower_eq_gap
import Theorems.Thm_QEC_Distillation_HH18_HH18SublogarithmicEntropy_p0_entropyGap_linear_form
import Theorems.Thm_QEC_Distillation_EncodedCode_ImplementsLogicalGate_symm


set_option autoImplicit false
open scoped BigOperators
open QEC QEC.Distillation QEC.Distillation.HH18 QEC.Distillation.HH18.HH18SublogarithmicEntropy
open Filter Topology
noncomputable section
namespace QEC.Distillation.HH18.HH18SublogarithmicEntropy
theorem _root_.solution : (1 / 1000 : ℝ) < p0EntropyGap := by
  have hlinear : p0LinearLower ≤ p0EntropyGap := by
    rw [p0_entropyGap_linear_form]
    unfold p0LinearLower
    nlinarith [p0_log2_upper, p0_logA_upper, p0_logB_lower,
      p0_logC_lower, p0_logD_lower]
  calc
    (1 / 1000 : ℝ) < (p0CertifiedGapQ : ℝ) := by
      calc
        (1 / 1000 : ℝ) = ((1 / 1000 : ℚ) : ℝ) := by norm_num [Rat.cast_div]
        _ < (p0CertifiedGapQ : ℝ) := by
          exact_mod_cast p0CertifiedGapQ_gt_thousandth
    _ = p0LinearLower := p0LinearLower_eq_gap.symm
    _ ≤ p0EntropyGap := hlinear
end QEC.Distillation.HH18.HH18SublogarithmicEntropy
