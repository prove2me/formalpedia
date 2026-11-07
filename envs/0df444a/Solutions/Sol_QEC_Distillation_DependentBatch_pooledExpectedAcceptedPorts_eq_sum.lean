-- Prove2me | solution 1 for QEC.Distillation.DependentBatch.pooledExpectedAcceptedPorts_eq_sum
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T15:19:28.357046+00:00
-- url     : https://prove2.me/submissions/2c4a8142-0423-446b-888b-d12d2d2ee52e

import Definitions.Def_QEC_Distillation_Core_Overhead
import Definitions.Def_QEC_Distillation_Core_DependentBatch

set_option autoImplicit false
noncomputable section
open QEC QEC.Distillation QEC.Distillation.DependentBatch
open Semantics
open scoped BigOperators
universe u v
namespace QEC.Distillation.DependentBatch
theorem _root_.solution {Port : Type u} {Outcome : Type v}
    [Fintype Port] [Fintype Outcome] (count : Nat)
    (pool : Fin count → FiniteFlaggedBatch Port Outcome) :
    pooledExpectedAcceptedPorts count pool =
      ∑ grid, expectedAcceptedPorts (pool grid) :=
  rfl
end QEC.Distillation.DependentBatch
