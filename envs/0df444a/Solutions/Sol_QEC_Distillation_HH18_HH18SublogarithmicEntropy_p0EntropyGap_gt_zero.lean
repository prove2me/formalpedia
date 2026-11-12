-- Prove2me | solution 1 for QEC.Distillation.HH18.HH18SublogarithmicEntropy.p0EntropyGap_gt_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-12T05:11:12.604903+00:00
-- url     : https://prove2.me/submissions/13f42345-96f3-428a-90e5-1d87750570b6

import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Sublogarithmic_BinomialTailAsymptotics
import Mathlib.Analysis.SpecialFunctions.BinaryEntropy
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Sublogarithmic_Entropy
import Theorems.Thm_QEC_Distillation_HH18_HH18SublogarithmicEntropy_p0EntropyGap_gt_thousandth

set_option autoImplicit false
open scoped BigOperators
open QEC QEC.Distillation QEC.Distillation.HH18 QEC.Distillation.HH18.HH18SublogarithmicEntropy
open Filter Topology
noncomputable section
namespace QEC.Distillation.HH18.HH18SublogarithmicEntropy
theorem _root_.solution : 0 < p0EntropyGap := by
  exact (by norm_num : (0 : ℝ) < 1 / 1000).trans p0EntropyGap_gt_thousandth
end QEC.Distillation.HH18.HH18SublogarithmicEntropy
