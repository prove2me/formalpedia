-- Prove2me | solution 1 for QEC.Distillation.Triorthogonal.BH12Concatenation.bh12PathSchedule_actualOutputError_le_targetError
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T22:39:22.024077+00:00
-- url     : https://prove2.me/submissions/e4825d55-45de-4d83-90f4-5e7a0be4a290

import Mathlib.Analysis.SpecificLimits.Basic
import Definitions.Def_QEC_Distillation_Triorthogonal_Protocol
import Definitions.Def_QEC_Distillation_Core_DependentBatch
import Definitions.Def_QEC_Distillation_Core_Overhead
import Definitions.Def_QEC_Distillation_Triorthogonal_Concatenation
import Theorems.Thm_QEC_Distillation_Triorthogonal_BH12Concatenation_bh12PathParameter_rate_le_quadraticEnvelope

set_option autoImplicit false
noncomputable section
open QEC QEC.Distillation QEC.Distillation.Triorthogonal QEC.Distillation.Triorthogonal.BH12Concatenation
open Semantics
open BH12EvenFamily
open BH12NoisyInjection
open BH12Protocol
open Filter Topology
namespace QEC.Distillation.Triorthogonal.BH12Concatenation
theorem _root_.solution (q : Nat)
    (p : ErrorParameter)
    (hsmall : (bh12InputCount q : ℝ) * p.rate ≤ 1 / 4)
    (hhalf : p.rate ≤ 1 / 2)
    (hstrong : quadraticCoefficient q * p.rate ≤ 1 / 2)
    (index : BH12PathScheduleIndex q) :
    (bh12PathParameter q p index.depth index.path).rate ≤
      bh12PathScheduleTargetError q p index := by
  exact bh12PathParameter_rate_le_quadraticEnvelope q p hsmall hhalf
    (hstrong.trans (by norm_num)) index.depth index.path
end QEC.Distillation.Triorthogonal.BH12Concatenation
