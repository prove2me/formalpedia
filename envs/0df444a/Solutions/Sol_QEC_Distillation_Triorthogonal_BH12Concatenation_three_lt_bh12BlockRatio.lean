-- Prove2me | solution 1 for QEC.Distillation.Triorthogonal.BH12Concatenation.three_lt_bh12BlockRatio
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T22:34:52.364434+00:00
-- url     : https://prove2.me/submissions/d103ee65-6eb0-4375-a68e-2728291326d5

import Mathlib.Analysis.SpecificLimits.Basic
import Definitions.Def_QEC_Distillation_Triorthogonal_Protocol
import Definitions.Def_QEC_Distillation_Core_DependentBatch
import Definitions.Def_QEC_Distillation_Core_Overhead
import Definitions.Def_QEC_Distillation_Triorthogonal_Concatenation
import Theorems.Thm_QEC_Distillation_Triorthogonal_BH12Concatenation_bh12OutputCount_pos
import Theorems.Thm_QEC_Distillation_Triorthogonal_BH12Concatenation_bh12BlockRatio_eq_three_add_eight_div_outputCount

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
    3 < bh12BlockRatio q := by
  rw [bh12BlockRatio_eq_three_add_eight_div_outputCount hq]
  have hk : 0 < (bh12OutputCount q : ℝ) := by
    exact_mod_cast bh12OutputCount_pos hq
  nlinarith [div_pos (by norm_num : (0 : ℝ) < 8) hk]
end QEC.Distillation.Triorthogonal.BH12Concatenation
