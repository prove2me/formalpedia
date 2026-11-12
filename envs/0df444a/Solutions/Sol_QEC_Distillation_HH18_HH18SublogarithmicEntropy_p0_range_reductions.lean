-- Prove2me | solution 1 for QEC.Distillation.HH18.HH18SublogarithmicEntropy.p0_range_reductions
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T15:36:10.482779+00:00
-- url     : https://prove2.me/submissions/93565218-54a2-49c9-b22a-7d46f3361fc4

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
    p0A = Real.log (1 + aA) ∧
      p0B = Real.log (1 + aB) ∧
      p0C = Real.log (1 + aC) ∧
      p0D = Real.log (1 + aD) := by
  constructor
  · norm_num [p0A, p0R, p0Q, aA, HH18ParameterSequence.p0]
  constructor
  · norm_num [p0B, p0R, p0Q, p0q, aB, HH18ParameterSequence.p0]
  constructor
  · norm_num [p0C, p0R, p0Q, p0u, p0v, aC, HH18ParameterSequence.p0]
  · norm_num [p0D, p0R, p0Q, p0u, p0v, aD, HH18ParameterSequence.p0]
end QEC.Distillation.HH18.HH18SublogarithmicEntropy
