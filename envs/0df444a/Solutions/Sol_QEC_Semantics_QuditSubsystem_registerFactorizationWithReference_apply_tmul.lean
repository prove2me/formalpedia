-- Prove2me | solution 1 for QEC.Semantics.QuditSubsystem.registerFactorizationWithReference_apply_tmul
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T12:42:50.780388+00:00
-- url     : https://prove2.me/submissions/af2ca8c1-1d9c-4fe3-9789-7c81f834c588

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
    (global : Qudit.QuditRegister q) (ref : Ref) :
    S.registerFactorizationWithReference Ref (global ⊗ₜ[Complex] ref) =
      (S.registerFactorization global) ⊗ₜ[Complex] ref := by
  rfl
end QEC.Semantics.QuditSubsystem
