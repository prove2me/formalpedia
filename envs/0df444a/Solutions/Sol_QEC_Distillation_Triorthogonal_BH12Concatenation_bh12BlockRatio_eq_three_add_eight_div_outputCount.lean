-- Prove2me | solution 1 for QEC.Distillation.Triorthogonal.BH12Concatenation.bh12BlockRatio_eq_three_add_eight_div_outputCount
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T22:28:28.487466+00:00
-- url     : https://prove2.me/submissions/7619b45d-2bf1-40aa-9e42-45518f322e61

import Mathlib.Analysis.SpecificLimits.Basic
import Definitions.Def_QEC_Distillation_Triorthogonal_Protocol
import Definitions.Def_QEC_Distillation_Core_DependentBatch
import Definitions.Def_QEC_Distillation_Core_Overhead
import Definitions.Def_QEC_Distillation_Triorthogonal_Concatenation
import Theorems.Thm_QEC_Distillation_Triorthogonal_BH12Concatenation_bh12InputCount_eq_three_mul_output_add_eight
import Theorems.Thm_QEC_Distillation_Triorthogonal_BH12Concatenation_bh12OutputCount_pos

set_option autoImplicit false
noncomputable section
open QEC QEC.Distillation QEC.Distillation.Triorthogonal QEC.Distillation.Triorthogonal.BH12Concatenation
open Semantics
open BH12EvenFamily
open BH12NoisyInjection
open BH12Protocol
open Filter Topology
namespace QEC.Distillation.Triorthogonal.BH12Concatenation
theorem _root_.solution {q : Nat}
    (hq : 0 < q) :
    bh12BlockRatio q = 3 + 8 / (bh12OutputCount q : ℝ) := by
  unfold bh12BlockRatio
  rw [bh12InputCount_eq_three_mul_output_add_eight]
  push_cast
  field_simp [ne_of_gt (by exact_mod_cast bh12OutputCount_pos hq)]
end QEC.Distillation.Triorthogonal.BH12Concatenation
