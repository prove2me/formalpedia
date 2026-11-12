-- Prove2me | solution 1 for QEC.Distillation.HH18.HH18SublogarithmicEntropy.p0_entropyGap_linear_form
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T21:37:41.199664+00:00
-- url     : https://prove2.me/submissions/ba6e01a7-6ea8-4469-bb21-b38f51da0615

import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Sublogarithmic_BinomialTailAsymptotics
import Mathlib.Analysis.SpecialFunctions.BinaryEntropy
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Sublogarithmic_Entropy
import Theorems.Thm_QEC_Distillation_HH18_HH18SublogarithmicEntropy_p0_entropy_expansions

set_option autoImplicit false
open scoped BigOperators
open QEC QEC.Distillation QEC.Distillation.HH18 QEC.Distillation.HH18.HH18SublogarithmicEntropy
open Filter Topology
noncomputable section
namespace QEC.Distillation.HH18.HH18SublogarithmicEntropy
theorem _root_.solution :
    p0EntropyGap =
      - (280286193 / 500000 : ℝ) * Real.log 2
      - (811887 / 2000 : ℝ) * p0A
      + (2188113 / 2000 : ℝ) * p0B
      + (275229693 / 1000000 : ℝ) * p0C
      + (63770307 / 1000000 : ℝ) * p0D := by
  rcases p0_entropy_expansions with ⟨hp, hu⟩
  unfold p0EntropyGap
  rw [hp, hu]
  norm_num [p0R, p0Q, p0q, p0u, p0v, HH18ParameterSequence.p0]
  ring
end QEC.Distillation.HH18.HH18SublogarithmicEntropy
