-- Prove2me | solution 1 for QEC.Semantics.QuditSubsystem.selectedReferenceTransport_apply_tmul
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T12:42:52.995818+00:00
-- url     : https://prove2.me/submissions/b6060a55-fd9b-4b98-ba84-3ede8b73068b

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
    S.selectedReferenceTransport Ref (global ⊗ₜ[Complex] ref) =
      S.selectedReferenceReordering Ref ((S.registerFactorization global) ⊗ₜ[Complex] ref) := by
  rfl
end QEC.Semantics.QuditSubsystem
