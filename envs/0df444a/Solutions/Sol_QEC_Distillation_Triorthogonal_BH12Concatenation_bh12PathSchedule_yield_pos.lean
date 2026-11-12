-- Prove2me | solution 1 for QEC.Distillation.Triorthogonal.BH12Concatenation.bh12PathSchedule_yield_pos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T22:32:57.132388+00:00
-- url     : https://prove2.me/submissions/67f78ff8-1f13-4292-a981-3f75dd47f36a

import Mathlib.Analysis.SpecificLimits.Basic
import Definitions.Def_QEC_Distillation_Triorthogonal_Protocol
import Definitions.Def_QEC_Distillation_Core_DependentBatch
import Definitions.Def_QEC_Distillation_Core_Overhead
import Definitions.Def_QEC_Distillation_Triorthogonal_Concatenation

set_option autoImplicit false
noncomputable section
open QEC QEC.Distillation QEC.Distillation.Triorthogonal QEC.Distillation.Triorthogonal.BH12Concatenation
open Semantics
open BH12EvenFamily
open BH12NoisyInjection
open BH12Protocol
open Filter Topology
namespace QEC.Distillation.Triorthogonal.BH12Concatenation
theorem _root_.solution (q : Nat) (p : ErrorParameter)
    (hsmall : (bh12InputCount q : ℝ) * p.rate ≤ 1 / 4)
    (hhalf : p.rate ≤ 1 / 2)
    (hstrong : quadraticCoefficient q * p.rate ≤ 1 / 2)
    (index : BH12PathScheduleIndex q) :
    0 < (bh12PathScheduleTypedYieldFactor q p hsmall hhalf hstrong index : ℝ) := by
  change 0 < bh12PathYieldFactorProduct q p index.depth index.path
  exact bh12PathYieldFactorProduct_pos q p hsmall hhalf hstrong
    index.depth index.path
end QEC.Distillation.Triorthogonal.BH12Concatenation
