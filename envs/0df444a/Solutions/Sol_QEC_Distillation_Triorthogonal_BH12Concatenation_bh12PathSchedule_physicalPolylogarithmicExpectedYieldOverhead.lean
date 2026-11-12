-- Prove2me | solution 1 for QEC.Distillation.Triorthogonal.BH12Concatenation.bh12PathSchedule_physicalPolylogarithmicExpectedYieldOverhead
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T22:58:33.054208+00:00
-- url     : https://prove2.me/submissions/870fc5f8-49e2-4621-b354-eb670716d431

import Mathlib.Analysis.SpecificLimits.Basic
import Definitions.Def_QEC_Distillation_Triorthogonal_Protocol
import Definitions.Def_QEC_Distillation_Core_DependentBatch
import Definitions.Def_QEC_Distillation_Core_Overhead
import Definitions.Def_QEC_Distillation_Triorthogonal_Concatenation
import Theorems.Thm_QEC_Distillation_Triorthogonal_BH12Concatenation_bh12PathSchedule_actualOutputError_le_targetError
import Theorems.Thm_QEC_Distillation_Triorthogonal_BH12Concatenation_bh12PathSchedule_typedPolylogCostBound

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
    (q : Nat) (p : ErrorParameter)
    (hsmall : (bh12InputCount q : ℝ) * p.rate ≤ 1 / 4)
    (hhalf : p.rate ≤ 1 / 2)
    (hstrong : quadraticCoefficient q * p.rate ≤ 1 / 2)
    (hp : 0 < p.rate) (hq : 0 < q) :
    DependentBatch.physicalPolylogarithmicExpectedYieldOverhead
      (bh12PathScheduleInputSlots q) (bh12PathScheduleOutputSlots q)
      (bh12PathScheduleTargetError q p)
      (fun index => (bh12PathParameter q p index.depth index.path).rate)
      (bh12PathScheduleTypedYieldFactor q p hsmall hhalf hstrong)
      (bh12BlockExponent q) (bh12QuadraticEnvelopeCostCoefficient q p) := by
  rcases bh12PathSchedule_typedPolylogCostBound q p hsmall hhalf hstrong hp hq with
    ⟨hcoefficient, hcost⟩
  refine ⟨hcoefficient, ?_⟩
  intro index htargetPos htargetLtOne
  obtain ⟨hyield, hcostBound⟩ := hcost index htargetPos htargetLtOne
  exact ⟨bh12PathSchedule_actualOutputError_le_targetError q p hsmall hhalf
    hstrong index, hyield, hcostBound⟩
end QEC.Distillation.Triorthogonal.BH12Concatenation
