-- Prove2me | solution 1 for QEC.Distillation.HH18.HH18SublogarithmicEntropy.p0CertifiedGapQ_between
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-12T05:10:15.501039+00:00
-- url     : https://prove2.me/submissions/7189fe58-599f-47d6-94e4-d36c6f36af99

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
theorem _root_.solution :
    10869 / 10000000 < p0CertifiedGapQ ∧
      p0CertifiedGapQ < 1087 / 1000000 := by
  norm_num [p0CertifiedGapQ, s1Q, s3Q, s4Q, y2Q, yAQ, yBQ, yCQ, yDQ]
end QEC.Distillation.HH18.HH18SublogarithmicEntropy
