-- Prove2me | solution 1 for QEC.Distillation.Triorthogonal.BH12Concatenation.bh12PathSchedule_typedPolylogCostBound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T22:54:43.652201+00:00
-- url     : https://prove2.me/submissions/490cfc84-7154-4bcc-8bd3-2ed04abcd6b3

import Mathlib.Analysis.SpecificLimits.Basic
import Definitions.Def_QEC_Distillation_Triorthogonal_Protocol
import Definitions.Def_QEC_Distillation_Core_DependentBatch
import Definitions.Def_QEC_Distillation_Core_Overhead
import Definitions.Def_QEC_Distillation_Triorthogonal_Concatenation
import Theorems.Thm_QEC_Distillation_Triorthogonal_BH12Concatenation_bh12QuadraticEnvelopeCostCoefficient_pos
import Theorems.Thm_QEC_Distillation_Triorthogonal_BH12Concatenation_bh12PathTypedSuccessfulOutputCost_le_quadraticEnvelope_polylog
import Theorems.Thm_QEC_Distillation_Triorthogonal_BH12Concatenation_bh12PathSchedule_yield_pos

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
    (hp : 0 < p.rate) (hq : 0 < q) :
    DependentBatch.typedPolylogCostBound (bh12PathScheduleInputSlots q)
      (bh12PathScheduleOutputSlots q) (bh12PathScheduleTargetError q p)
      (bh12PathScheduleTypedYieldFactor q p hsmall hhalf hstrong)
      (bh12BlockExponent q) (bh12QuadraticEnvelopeCostCoefficient q p) := by
  refine ⟨(bh12QuadraticEnvelopeCostCoefficient_pos q p hp hstrong).le, ?_⟩
  intro index _ _
  refine ⟨bh12PathSchedule_yield_pos q p hsmall hhalf hstrong index, ?_⟩
  exact bh12PathTypedSuccessfulOutputCost_le_quadraticEnvelope_polylog q p hsmall
    hhalf hstrong hp hq index.depth index.path
end QEC.Distillation.Triorthogonal.BH12Concatenation
