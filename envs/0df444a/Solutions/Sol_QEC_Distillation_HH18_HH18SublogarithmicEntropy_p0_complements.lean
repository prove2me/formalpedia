-- Prove2me | solution 1 for QEC.Distillation.HH18.HH18SublogarithmicEntropy.p0_complements
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T16:00:17.583556+00:00
-- url     : https://prove2.me/submissions/87474f60-cb1f-4139-be45-3ae9ef63d3f5

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
    p0q = 729371 / 1000000 ∧
      p0u = 811887 / 1000000 ∧
      p0v = 188113 / 1000000 ∧
      0 < p0u ∧ p0u < 1 ∧ 0 < p0v ∧ p0v < 1 := by
  norm_num [p0R, p0Q, p0q, p0u, p0v, HH18ParameterSequence.p0]
end QEC.Distillation.HH18.HH18SublogarithmicEntropy
