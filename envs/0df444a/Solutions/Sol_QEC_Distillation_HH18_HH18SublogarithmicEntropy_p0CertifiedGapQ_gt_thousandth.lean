-- Prove2me | solution 1 for QEC.Distillation.HH18.HH18SublogarithmicEntropy.p0CertifiedGapQ_gt_thousandth
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T21:27:38.324357+00:00
-- url     : https://prove2.me/submissions/1ee6e0b7-221d-4cd8-b6d0-00da839e0232

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
theorem _root_.solution : (1 / 1000 : ℚ) < p0CertifiedGapQ := by
  norm_num [p0CertifiedGapQ, s1Q, s3Q, s4Q, y2Q, yAQ, yBQ, yCQ, yDQ]
end QEC.Distillation.HH18.HH18SublogarithmicEntropy
