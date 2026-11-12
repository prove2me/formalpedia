-- Prove2me | solution 1 for QEC.Distillation.HH18.HH18SublogarithmicEntropy.p0Gamma_denominator_pos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-12T05:12:25.648199+00:00
-- url     : https://prove2.me/submissions/1421b1d9-17f9-4184-b843-42db948b9e05

import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Sublogarithmic_BinomialTailAsymptotics
import Mathlib.Analysis.SpecialFunctions.BinaryEntropy
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Sublogarithmic_Entropy
import Theorems.Thm_QEC_Distillation_HH18_HH18SublogarithmicEntropy_p0_binEntropy_u_pos

set_option autoImplicit false
open scoped BigOperators
open QEC QEC.Distillation QEC.Distillation.HH18 QEC.Distillation.HH18.HH18SublogarithmicEntropy
open Filter Topology
noncomputable section
namespace QEC.Distillation.HH18.HH18SublogarithmicEntropy
theorem _root_.solution :
    0 < hh18BinaryEntropy (3 * p0R) := by
  change 0 < Real.binEntropy p0u / Real.log 2
  exact div_pos p0_binEntropy_u_pos (Real.log_pos one_lt_two)
end QEC.Distillation.HH18.HH18SublogarithmicEntropy
