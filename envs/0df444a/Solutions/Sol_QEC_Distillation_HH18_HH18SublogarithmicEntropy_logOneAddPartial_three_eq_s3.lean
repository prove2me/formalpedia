-- Prove2me | solution 1 for QEC.Distillation.HH18.HH18SublogarithmicEntropy.logOneAddPartial_three_eq_s3
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T15:42:42.0514+00:00
-- url     : https://prove2.me/submissions/49c410a7-983a-4713-a1c5-1fc74b070c29

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
theorem _root_.solution (a : ℝ) :
    logOneAddPartial a 3 = s3 (a / (a + 2)) := by
  norm_num [logOneAddPartial, logOneAddTerm, Finset.sum_range_succ, s3]
  ring
end QEC.Distillation.HH18.HH18SublogarithmicEntropy
