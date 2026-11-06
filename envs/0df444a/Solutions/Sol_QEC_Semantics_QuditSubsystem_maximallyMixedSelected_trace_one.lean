-- Prove2me | solution 1 for QEC.Semantics.QuditSubsystem.maximallyMixedSelected_trace_one
-- status  : ACCEPTED   (prove)
-- author  : @dphz
-- created : 2026-11-05T17:48:16.977128+00:00
-- url     : https://prove2.me/submissions/f3e15c8b-597c-49da-8087-4a5fd62cd139

-- ID: f5d49ed9-5299-4509-baaa-49393ba8dc75 | NAME: QEC.Semantics.QuditSubsystem.maximallyMixedSelected_trace_one | 未本地编译验证
import Definitions.Def_QEC_Semantics_ErrorCorrection_QuditSubsystem
import Definitions.Def_QEC_Semantics_Channels_Kraus
import Definitions.Def_QEC_Semantics_ErrorCorrection_QuditReplacement
set_option autoImplicit false
noncomputable section
open QEC
open QEC.Semantics
open QEC.Semantics.QuditSubsystem
open Classical
open scoped BigOperators ComplexOrder TensorProduct
universe u v
variable {ι : Type u} [Fintype ι] [DecidableEq ι]
variable {q : ι → Nat}

theorem solution (S : QuditSubsystem q) (hq : ∀ i, 0 < q i) :
    LinearMap.trace Complex S.selectedSystem (S.maximallyMixedSelected hq).toOperator = 1 := by
  exact (S.maximallyMixedSelected hq).trace_one
