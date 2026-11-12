-- Prove2me | solution 1 for QEC.Distillation.HH18.HH18SublogarithmicEntropy.logOneAddPartial_one_eq_s1
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T16:39:30.338782+00:00
-- url     : https://prove2.me/submissions/948cebb3-60a1-4076-aa18-7b6a55d18f80

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
    logOneAddPartial a 1 = s1 (a / (a + 2)) := by
  norm_num [logOneAddPartial, logOneAddTerm, Finset.sum_range_succ, s1]
end QEC.Distillation.HH18.HH18SublogarithmicEntropy
