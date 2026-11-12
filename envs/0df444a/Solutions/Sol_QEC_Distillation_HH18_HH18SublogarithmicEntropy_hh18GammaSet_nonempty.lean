-- Prove2me | solution 1 for QEC.Distillation.HH18.HH18SublogarithmicEntropy.hh18GammaSet_nonempty
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T16:38:36.908017+00:00
-- url     : https://prove2.me/submissions/8bd7a523-4d9e-48df-9342-6038cbf40888

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
theorem _root_.solution : hh18GammaSet.Nonempty := by
  refine ⟨hh18Gamma (1 / 4 : ℝ), ?_⟩
  refine ⟨(1 / 4 : ℝ), ?_, rfl⟩
  norm_num [hh18GammaSet, hh18ParameterInterval]
end QEC.Distillation.HH18.HH18SublogarithmicEntropy
