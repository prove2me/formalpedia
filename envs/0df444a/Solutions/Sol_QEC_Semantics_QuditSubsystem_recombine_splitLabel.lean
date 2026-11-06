-- Prove2me | solution 1 for QEC.Semantics.QuditSubsystem.recombine_splitLabel
-- status  : ACCEPTED   (prove)
-- author  : @dphz
-- created : 2026-11-05T17:51:36.562335+00:00
-- url     : https://prove2.me/submissions/5c9320f2-4db9-48d0-a86a-a8d3f022073c

-- ID: e70a0d39-ce71-4355-8aef-6dd6a5dfd11e | NAME: QEC.Semantics.QuditSubsystem.recombine_splitLabel | 未本地编译验证
import Definitions.Def_QEC_Semantics_Channels_Core
import Mathlib.Analysis.InnerProductSpace.PiL2
import Definitions.Def_QEC_Semantics_ErrorCorrection_QuditSubsystem
set_option autoImplicit false
noncomputable section
open QEC
open QEC.Semantics
open Classical
open scoped BigOperators ComplexOrder TensorProduct
universe u v
open QEC.Semantics.QuditSubsystem
variable {ι : Type u} [Fintype ι] [DecidableEq ι]
variable {q : ι → Nat}

theorem solution (S : QuditSubsystem q) (labels : Qudit.Label q) :
    S.recombineLabel (S.splitLabel labels) = labels := by
  funext i
  by_cases hi : i ∈ S.selected <;> simp [splitLabel, recombineLabel, hi]
