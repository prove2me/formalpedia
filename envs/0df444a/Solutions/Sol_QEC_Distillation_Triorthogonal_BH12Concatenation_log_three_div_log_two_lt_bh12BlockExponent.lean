-- Prove2me | solution 1 for QEC.Distillation.Triorthogonal.BH12Concatenation.log_three_div_log_two_lt_bh12BlockExponent
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T22:38:35.91276+00:00
-- url     : https://prove2.me/submissions/cf3ec59c-e3e4-4354-accf-ac61dcc87d8d

import Mathlib.Analysis.SpecificLimits.Basic
import Definitions.Def_QEC_Distillation_Triorthogonal_Protocol
import Definitions.Def_QEC_Distillation_Core_DependentBatch
import Definitions.Def_QEC_Distillation_Core_Overhead
import Definitions.Def_QEC_Distillation_Triorthogonal_Concatenation
import Theorems.Thm_QEC_Distillation_Triorthogonal_BH12Concatenation_three_lt_bh12BlockRatio

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
    Real.log 3 / Real.log 2 < bh12BlockExponent q := by
  have hratio : 3 < bh12BlockRatio q := three_lt_bh12BlockRatio hq
  have hratioPos : 0 < bh12BlockRatio q := lt_trans (by norm_num) hratio
  have hlog : Real.log 3 < Real.log (bh12BlockRatio q) :=
    Real.strictMonoOn_log (by norm_num) hratioPos hratio
  unfold bh12BlockExponent
  exact (div_lt_div_iff_of_pos_right (Real.log_pos (by norm_num))).mpr hlog
end QEC.Distillation.Triorthogonal.BH12Concatenation
