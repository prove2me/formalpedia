-- Prove2me | solution 1 for QEC.Distillation.HH18.HH18SublogarithmicEntropy.p0_entropy_expansions
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T21:35:30.651296+00:00
-- url     : https://prove2.me/submissions/43076c65-fb95-4d69-9b4c-3b25fad66cc1

import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Sublogarithmic_BinomialTailAsymptotics
import Mathlib.Analysis.SpecialFunctions.BinaryEntropy
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Sublogarithmic_Entropy
import Theorems.Thm_QEC_Distillation_HH18_HH18SublogarithmicEntropy_binEntropy_eq_log_inv_form
import Theorems.Thm_QEC_Distillation_HH18_HH18SublogarithmicEntropy_p0_inverse_log_reductions

set_option autoImplicit false
open scoped BigOperators
open QEC QEC.Distillation QEC.Distillation.HH18 QEC.Distillation.HH18.HH18SublogarithmicEntropy
open Filter Topology
noncomputable section
namespace QEC.Distillation.HH18.HH18SublogarithmicEntropy
theorem _root_.solution :
    Real.binEntropy p0R = p0R * (2 * Real.log 2 - p0A) + p0q * p0B ∧
      Real.binEntropy p0u = p0u * p0C + p0v * (2 * Real.log 2 + p0D) := by
  rcases p0_inverse_log_reductions with ⟨hp, hq, hu, hv⟩
  constructor
  · rw [binEntropy_eq_log_inv_form, hp]
    change p0R * (2 * Real.log 2 - p0A) + p0q * Real.log (1 / p0q) =
      p0R * (2 * Real.log 2 - p0A) + p0q * p0B
    rw [hq]
  · rw [binEntropy_eq_log_inv_form, hu]
    change p0u * p0C + p0v * Real.log (1 / p0v) =
      p0u * p0C + p0v * (2 * Real.log 2 + p0D)
    rw [hv]
end QEC.Distillation.HH18.HH18SublogarithmicEntropy
