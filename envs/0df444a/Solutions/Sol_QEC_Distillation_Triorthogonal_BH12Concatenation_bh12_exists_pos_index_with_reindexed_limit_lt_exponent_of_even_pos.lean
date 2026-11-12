-- Prove2me | solution 1 for QEC.Distillation.Triorthogonal.BH12Concatenation.bh12_exists_pos_index_with_reindexed_limit_lt_exponent_of_even_pos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T22:41:22.498218+00:00
-- url     : https://prove2.me/submissions/c683f898-3af6-4bfe-a8c3-05302dc5a089

import Mathlib.Analysis.SpecificLimits.Basic
import Definitions.Def_QEC_Distillation_Triorthogonal_Protocol
import Definitions.Def_QEC_Distillation_Core_DependentBatch
import Definitions.Def_QEC_Distillation_Core_Overhead
import Definitions.Def_QEC_Distillation_Triorthogonal_Concatenation
import Theorems.Thm_QEC_Distillation_Triorthogonal_BH12Concatenation_log_three_div_log_two_lt_bh12BlockExponent
import Theorems.Thm_QEC_Distillation_Triorthogonal_BH12Concatenation_bh12_exists_pos_index_of_even_pos
import Theorems.Thm_QEC_Distillation_Triorthogonal_BH12Concatenation_bh12BlockExponent_eq_log_countRatio_of_logicalCount_eq

set_option autoImplicit false
noncomputable section
open QEC QEC.Distillation QEC.Distillation.Triorthogonal QEC.Distillation.Triorthogonal.BH12Concatenation
open Semantics
open BH12EvenFamily
open BH12NoisyInjection
open BH12Protocol
open Filter Topology
namespace QEC.Distillation.Triorthogonal.BH12Concatenation
theorem _root_.solution
    {k : Nat} (hk : Even k) (hpos : 0 < k) :
    ∃ q : Nat, 0 < q ∧ k = logicalCount q ∧
      bh12BlockExponent q =
        Real.log (((3 * k + 8 : Nat) : ℝ) / (k : ℝ)) / Real.log 2 ∧
      Real.log 3 / Real.log 2 < bh12BlockExponent q := by
  obtain ⟨q, hq, hlogicalCount⟩ := bh12_exists_pos_index_of_even_pos hk hpos
  exact ⟨q, hq, hlogicalCount,
    bh12BlockExponent_eq_log_countRatio_of_logicalCount_eq hq hlogicalCount,
    log_three_div_log_two_lt_bh12BlockExponent hq⟩
end QEC.Distillation.Triorthogonal.BH12Concatenation
