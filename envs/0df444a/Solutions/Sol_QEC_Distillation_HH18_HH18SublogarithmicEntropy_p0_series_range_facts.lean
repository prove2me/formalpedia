-- Prove2me | solution 1 for QEC.Distillation.HH18.HH18SublogarithmicEntropy.p0_series_range_facts
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-12T05:09:53.378735+00:00
-- url     : https://prove2.me/submissions/f05a02ba-7577-42da-9aa2-23f3cc04cc0d

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
    0 ≤ yA ∧ yA ≤ 1 / 25 ∧
      0 ≤ yB ∧ yB < 1 ∧
      0 ≤ yC ∧ yC < 1 ∧
      0 ≤ yD ∧ yD < 1 := by
  norm_num [yA, yB, yC, yD]
end QEC.Distillation.HH18.HH18SublogarithmicEntropy
