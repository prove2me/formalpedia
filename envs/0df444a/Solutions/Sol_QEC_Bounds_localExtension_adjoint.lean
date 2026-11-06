-- Prove2me | solution 1 for QEC.Bounds.localExtension_adjoint
-- status  : ACCEPTED   (prove)
-- author  : @dphz
-- created : 2026-11-05T18:10:42.699201+00:00
-- url     : https://prove2.me/submissions/ef35b38c-8679-4979-9869-e4f0bf422286

-- ID: 4de5e785-2683-4e92-aca5-df3231f9ca57 | NAME: QEC.Bounds.localExtension_adjoint | 未本地编译验证
import Definitions.Def_QEC_Semantics_ErrorCorrection_CodeSupport
import Definitions.Def_QEC_Semantics_ErrorCorrection_QuditSubsystem
import Definitions.Def_QEC_Bounds_GeometricLocalityTradeoff_Model
set_option autoImplicit false
noncomputable section
open QEC
open QEC.Bounds
open Classical
open scoped BigOperators
universe u v

theorem solution {ι : Type u} [Fintype ι] [DecidableEq ι]
    {q : ι → Nat} (S : Semantics.QuditSubsystem q)
    (A : Semantics.Operator S.selectedSystem) :
    LinearMap.adjoint (S.extendLocalToRegister A) =
      S.extendLocalToRegister (LinearMap.adjoint A) := by
  solve
    | simp [QEC.Semantics.QuditSubsystem.extendLocalToRegister,
        QEC.Semantics.QuditSubsystem.extendLocal, LinearMap.adjoint_id]
    | simp [QEC.Semantics.QuditSubsystem.extendLocalToRegister,
        QEC.Semantics.QuditSubsystem.extendLocal]
