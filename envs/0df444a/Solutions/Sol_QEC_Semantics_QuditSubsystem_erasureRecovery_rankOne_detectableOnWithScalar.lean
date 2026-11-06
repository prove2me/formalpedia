-- Prove2me | solution 1 for QEC.Semantics.QuditSubsystem.erasureRecovery_rankOne_detectableOnWithScalar
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T14:06:11.483945+00:00
-- url     : https://prove2.me/submissions/04556efa-4a5a-40d7-b0a1-6425fd3e60f3

import Definitions.Def_QEC_Semantics_Entropy_Purification
import Definitions.Def_QEC_Semantics_Entropy_MatrixRelative
import Definitions.Def_QEC_Semantics_ErrorCorrection_QuditReplacement
import Definitions.Def_QEC_Semantics_ErrorCorrection_KLRecovery
import Definitions.Def_QEC_Semantics_ErrorCorrection_Detectability
import Definitions.Def_QEC_Semantics_ErrorCorrection_ReferenceDecoupling
import Theorems.Thm_QEC_Semantics_QuditSubsystem_erasureKraus_adjoint_comp
import Theorems.Thm_QEC_Semantics_QuditSubsystem_erasureRecovery_matrixElement_scalars
import Theorems.Thm_QEC_Semantics_QuantumChannel_comp_apply
attribute [local simp] QEC.Semantics.QuantumChannel.comp_apply



set_option autoImplicit false
noncomputable section
open QEC
open QEC.Semantics
open Classical
open DensityOperator
open scoped BigOperators ComplexOrder TensorProduct
universe u v w
open QEC.Semantics.QuditSubsystem
variable {ι : Type u} [Fintype ι] [DecidableEq ι]
variable {q : ι → Nat}
namespace QEC.Semantics.QuditSubsystem
theorem _root_.solution (S : QuditSubsystem q)
    (C : QuantumCode (Qudit.QuditRegister q))
    (recovery : QuantumChannel S.complementSystem (Qudit.QuditRegister q))
    (hcorrect : Correctable (Qudit.QuditRegister q) S.complementSystem C
      S.erasureChannelFromRegister recovery)
    (i j : Fin (Module.finrank Complex S.selectedSystem)) :
    ∃ scalar : Complex,
      DetectableOnWithScalar C
        (S.extendLocalToRegister (InnerProductSpace.rankOne Complex
          ((stdOrthonormalBasis Complex S.selectedSystem) i)
          ((stdOrthonormalBasis Complex S.selectedSystem) j)).toLinearMap)
        scalar := by
  rcases S.erasureRecovery_matrixElement_scalars C recovery hcorrect with ⟨scalar, hscalar⟩
  refine ⟨scalar i j, ?_⟩
  intro x hx y hy
  calc
    inner Complex x
        (S.extendLocalToRegister (InnerProductSpace.rankOne Complex
          ((stdOrthonormalBasis Complex S.selectedSystem) i)
          ((stdOrthonormalBasis Complex S.selectedSystem) j)).toLinearMap y) =
        inner Complex x
          (((LinearMap.adjoint ((S.erasureKraus).operator i)).comp
            ((S.erasureKraus).operator j)) y) := by
              rw [S.erasureKraus_adjoint_comp i j]
    _ = inner Complex ((S.erasureKraus).operator i x)
          ((S.erasureKraus).operator j y) := by
            rw [LinearMap.comp_apply]
            exact LinearMap.adjoint_inner_right (𝕜 := Complex)
              ((S.erasureKraus).operator i) x ((S.erasureKraus).operator j y)
    _ = scalar i j * inner Complex x y := hscalar i j x hx y hy
end QEC.Semantics.QuditSubsystem
