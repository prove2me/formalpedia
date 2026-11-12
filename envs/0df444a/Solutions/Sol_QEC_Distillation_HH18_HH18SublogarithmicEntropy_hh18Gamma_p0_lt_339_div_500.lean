-- Prove2me | solution 1 for QEC.Distillation.HH18.HH18SublogarithmicEntropy.hh18Gamma_p0_lt_339_div_500
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T21:43:18.184744+00:00
-- url     : https://prove2.me/submissions/a1acf5e7-ec14-4c45-8444-106b4f02b9e2

import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Sublogarithmic_BinomialTailAsymptotics
import Mathlib.Analysis.SpecialFunctions.BinaryEntropy
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Sublogarithmic_Entropy
import Theorems.Thm_QEC_Distillation_HH18_HH18SublogarithmicEntropy_p0_binEntropy_u_pos
import Theorems.Thm_QEC_Distillation_HH18_HH18SublogarithmicEntropy_p0EntropyGap_gt_thousandth

set_option autoImplicit false
open scoped BigOperators
open QEC QEC.Distillation QEC.Distillation.HH18 QEC.Distillation.HH18.HH18SublogarithmicEntropy
open Filter Topology
noncomputable section
namespace QEC.Distillation.HH18.HH18SublogarithmicEntropy
theorem _root_.solution :
    hh18Gamma p0R < (339 / 500 : ℝ) := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hHu : 0 < Real.binEntropy p0u := p0_binEntropy_u_pos
  have hden : 0 < Real.binEntropy p0u / Real.log 2 := div_pos hHu hlog2
  change 3 * (1 - Real.binEntropy p0R / Real.log 2) /
      (Real.binEntropy p0u / Real.log 2) < (339 / 500 : ℝ)
  apply (div_lt_iff₀ hden).mpr
  field_simp [hlog2.ne', hHu.ne']
  have hgap := p0EntropyGap_gt_thousandth
  unfold p0EntropyGap at hgap
  nlinarith [hgap]
end QEC.Distillation.HH18.HH18SublogarithmicEntropy
