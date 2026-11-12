-- Prove2me | solution 1 for QEC.Distillation.HH18.HH18SublogarithmicEntropy.logOneAddPartial_four_eq_s4
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T16:39:43.936204+00:00
-- url     : https://prove2.me/submissions/f89e6619-c516-493f-b352-320f0ac4d69f

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
    logOneAddPartial a 4 = s4 (a / (a + 2)) := by
  norm_num [logOneAddPartial, logOneAddTerm, Finset.sum_range_succ, s3, s4]
  ring
end QEC.Distillation.HH18.HH18SublogarithmicEntropy
