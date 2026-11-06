-- Prove2me | solution 1 for QEC.Semantics.QuditSubsystem.selectedReferenceReordering_apply_tmul
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T12:42:50.04382+00:00
-- url     : https://prove2.me/submissions/5d0c7c48-c8b8-4835-ae45-806ca6fe1d7e

import Definitions.Def_QEC_Semantics_Entropy_Purification
import Definitions.Def_QEC_Semantics_Entropy_MatrixRelative
import Definitions.Def_QEC_Semantics_ErrorCorrection_QuditReplacement
import Definitions.Def_QEC_Semantics_ErrorCorrection_KLRecovery
import Definitions.Def_QEC_Semantics_ErrorCorrection_Detectability
import Definitions.Def_QEC_Semantics_ErrorCorrection_ReferenceDecoupling

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
variable (S : QuditSubsystem q)
variable (Ref : Type u) [NormedAddCommGroup Ref] [InnerProductSpace Complex Ref]
    [FiniteQuantumSystem Ref]
namespace QEC.Semantics.QuditSubsystem
theorem _root_.solution
    (selected : S.selectedSystem) (complement : S.complementSystem) (ref : Ref) :
    S.selectedReferenceReordering Ref ((selected ⊗ₜ[Complex] complement) ⊗ₜ[Complex] ref) =
      (selected ⊗ₜ[Complex] ref) ⊗ₜ[Complex] complement := by
  rfl
end QEC.Semantics.QuditSubsystem
