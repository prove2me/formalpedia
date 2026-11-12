-- Prove2me | solution 1 for QEC.Distillation.Triorthogonal.BH12Concatenation.bh12BlockRatio_eq_countRatio_of_logicalCount_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T22:33:33.020202+00:00
-- url     : https://prove2.me/submissions/0b3014fd-41fc-415f-adb1-852727487309

import Mathlib.Analysis.SpecificLimits.Basic
import Definitions.Def_QEC_Distillation_Triorthogonal_Protocol
import Definitions.Def_QEC_Distillation_Core_DependentBatch
import Definitions.Def_QEC_Distillation_Core_Overhead
import Definitions.Def_QEC_Distillation_Triorthogonal_Concatenation
import Theorems.Thm_QEC_Distillation_Triorthogonal_BH12Concatenation_bh12InputCount_eq_three_mul_output_add_eight

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
    (_ : 0 < q) (hk : k = logicalCount q) :
    bh12BlockRatio q = ((3 * k + 8 : Nat) : ℝ) / (k : ℝ) := by
  subst k
  unfold bh12BlockRatio
  rw [bh12InputCount_eq_three_mul_output_add_eight]
  rfl
end QEC.Distillation.Triorthogonal.BH12Concatenation
