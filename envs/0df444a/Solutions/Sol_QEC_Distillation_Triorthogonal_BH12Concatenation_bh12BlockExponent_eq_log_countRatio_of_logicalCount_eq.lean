-- Prove2me | solution 1 for QEC.Distillation.Triorthogonal.BH12Concatenation.bh12BlockExponent_eq_log_countRatio_of_logicalCount_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T22:35:51.529832+00:00
-- url     : https://prove2.me/submissions/4aedecbd-712d-4fdc-8f8b-f459e3bd8975

import Mathlib.Analysis.SpecificLimits.Basic
import Definitions.Def_QEC_Distillation_Triorthogonal_Protocol
import Definitions.Def_QEC_Distillation_Core_DependentBatch
import Definitions.Def_QEC_Distillation_Core_Overhead
import Definitions.Def_QEC_Distillation_Triorthogonal_Concatenation
import Theorems.Thm_QEC_Distillation_Triorthogonal_BH12Concatenation_bh12BlockRatio_eq_countRatio_of_logicalCount_eq

set_option autoImplicit false
noncomputable section
open QEC QEC.Distillation QEC.Distillation.Triorthogonal QEC.Distillation.Triorthogonal.BH12Concatenation
open Semantics
open BH12EvenFamily
open BH12NoisyInjection
open BH12Protocol
open Filter Topology
namespace QEC.Distillation.Triorthogonal.BH12Concatenation
theorem _root_.solution {q k : Nat}
    (hq : 0 < q) (hk : k = logicalCount q) :
    bh12BlockExponent q =
      Real.log (((3 * k + 8 : Nat) : ℝ) / (k : ℝ)) / Real.log 2 := by
  unfold bh12BlockExponent
  rw [bh12BlockRatio_eq_countRatio_of_logicalCount_eq hq hk]
end QEC.Distillation.Triorthogonal.BH12Concatenation
