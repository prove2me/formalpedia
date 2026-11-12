-- Prove2me | solution 1 for QEC.Distillation.HH18.HH18SublogarithmicEntropy.hh18GammaInf_lt_339_div_500
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T21:46:52.258528+00:00
-- url     : https://prove2.me/submissions/a3050732-4272-4b8c-9281-57875f3cae2a

import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Sublogarithmic_BinomialTailAsymptotics
import Mathlib.Analysis.SpecialFunctions.BinaryEntropy
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Sublogarithmic_Entropy
import Theorems.Thm_QEC_Distillation_HH18_HH18SublogarithmicEntropy_hh18GammaSet_bddBelow
import Theorems.Thm_QEC_Distillation_HH18_HH18SublogarithmicEntropy_p0_mem_parameterInterval
import Theorems.Thm_QEC_Distillation_HH18_HH18SublogarithmicEntropy_hh18Gamma_p0_lt_339_div_500

set_option autoImplicit false
open scoped BigOperators
open QEC QEC.Distillation QEC.Distillation.HH18 QEC.Distillation.HH18.HH18SublogarithmicEntropy
open Filter Topology
noncomputable section
namespace QEC.Distillation.HH18.HH18SublogarithmicEntropy
theorem _root_.solution :
    hh18GammaInf < (339 / 500 : ℝ) := by
  refine lt_of_le_of_lt ?_ hh18Gamma_p0_lt_339_div_500
  rw [hh18GammaInf]
  exact csInf_le hh18GammaSet_bddBelow ⟨p0R, p0_mem_parameterInterval, rfl⟩
end QEC.Distillation.HH18.HH18SublogarithmicEntropy
