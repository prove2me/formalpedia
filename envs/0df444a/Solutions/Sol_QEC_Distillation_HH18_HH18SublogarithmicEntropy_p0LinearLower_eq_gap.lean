-- Prove2me | solution 1 for QEC.Distillation.HH18.HH18SublogarithmicEntropy.p0LinearLower_eq_gap
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T21:27:41.869207+00:00
-- url     : https://prove2.me/submissions/041a841a-d785-4308-858e-dda4c1685316

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
theorem _root_.solution : p0LinearLower = (p0CertifiedGapQ : ℝ) := by
  norm_num [p0LinearLower, logBLower, logCLower, logDLower, logAUpper,
    log2Upper, s1, s3, s4, y2, yA, yB, yC, yD, p0CertifiedGapQ,
    s1Q, s3Q, s4Q, y2Q, yAQ, yBQ, yCQ, yDQ]
end QEC.Distillation.HH18.HH18SublogarithmicEntropy
