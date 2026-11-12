-- Prove2me | solution 1 for QEC.Distillation.HH18.HH18SublogarithmicEntropy.hh18GammaInf_eq_sInf
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-12T05:09:28.632179+00:00
-- url     : https://prove2.me/submissions/9bca0966-5e2f-40e7-9633-b714d3661e07

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
theorem _root_.solution : hh18GammaInf = sInf hh18GammaSet := rfl
end QEC.Distillation.HH18.HH18SublogarithmicEntropy
