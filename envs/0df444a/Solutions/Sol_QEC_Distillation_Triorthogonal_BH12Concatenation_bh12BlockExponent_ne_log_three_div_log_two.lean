-- Prove2me | solution 1 for QEC.Distillation.Triorthogonal.BH12Concatenation.bh12BlockExponent_ne_log_three_div_log_two
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T22:41:19.343197+00:00
-- url     : https://prove2.me/submissions/a7474928-415e-4d4f-a028-f2808bdec09c

import Mathlib.Analysis.SpecificLimits.Basic
import Definitions.Def_QEC_Distillation_Triorthogonal_Protocol
import Definitions.Def_QEC_Distillation_Core_DependentBatch
import Definitions.Def_QEC_Distillation_Core_Overhead
import Definitions.Def_QEC_Distillation_Triorthogonal_Concatenation
import Theorems.Thm_QEC_Distillation_Triorthogonal_BH12Concatenation_log_three_div_log_two_lt_bh12BlockExponent

set_option autoImplicit false
noncomputable section
open QEC QEC.Distillation QEC.Distillation.Triorthogonal QEC.Distillation.Triorthogonal.BH12Concatenation
open Semantics
open BH12EvenFamily
open BH12NoisyInjection
open BH12Protocol
open Filter Topology
namespace QEC.Distillation.Triorthogonal.BH12Concatenation
theorem _root_.solution {q : Nat} (hq : 0 < q) :
    bh12BlockExponent q ≠ Real.log 3 / Real.log 2 :=
  ne_of_gt (log_three_div_log_two_lt_bh12BlockExponent hq)
end QEC.Distillation.Triorthogonal.BH12Concatenation
