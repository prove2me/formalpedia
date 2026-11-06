-- Prove2me | solution 1 for QEC.Semantics.QuditSubsystem.erasureRecovery_matrixElement_scalars
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T14:03:52.129246+00:00
-- url     : https://prove2.me/submissions/ca6fec14-4544-48af-a3c3-80340ffc1a33

import Definitions.Def_QEC_Semantics_Entropy_Purification
import Definitions.Def_QEC_Semantics_Entropy_MatrixRelative
import Definitions.Def_QEC_Semantics_ErrorCorrection_QuditReplacement
import Definitions.Def_QEC_Semantics_ErrorCorrection_KLRecovery
import Definitions.Def_QEC_Semantics_ErrorCorrection_Detectability
import Definitions.Def_QEC_Semantics_ErrorCorrection_ReferenceDecoupling
import Theorems.Thm_QEC_Semantics_FiniteKrausFamily_exists_heterogeneous_matrix_element_scalars_of_correctedBy
import Theorems.Thm_QEC_Semantics_QuditSubsystem_erasureKraus_inducedMap_eq_erasureChannelFromRegister
import Theorems.Thm_QEC_Semantics_QuantumChannel_exists_finiteKrausFamily_representation


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
      S.erasureChannelFromRegister recovery) :
    ∃ scalar : Fin (Module.finrank Complex S.selectedSystem) →
        Fin (Module.finrank Complex S.selectedSystem) → Complex,
      ∀ i j (x : Qudit.QuditRegister q), x ∈ C.carrier →
        ∀ y : Qudit.QuditRegister q, y ∈ C.carrier →
          inner Complex ((S.erasureKraus).operator i x)
            ((S.erasureKraus).operator j y) =
              scalar i j * inner Complex x y := by
  classical
  rcases QuantumChannel.exists_finiteKrausFamily_representation recovery with
    ⟨m, R, hR_complete, hR_map⟩
  apply FiniteKrausFamily.exists_heterogeneous_matrix_element_scalars_of_correctedBy
    S.erasureKraus C R.operator hR_complete
  intro rho hRho
  calc
    (∑ r : Fin m, (R.operator r).comp
        ((S.erasureKraus.inducedMap rho.toOperator).comp
          (LinearMap.adjoint (R.operator r)))) =
        R.inducedMap (S.erasureKraus.inducedMap rho.toOperator) := by
          exact (FiniteKrausFamily.inducedMap_apply R
            (S.erasureKraus.inducedMap rho.toOperator)).symm
    _ = recovery.toLinearMap (S.erasureKraus.inducedMap rho.toOperator) := by
          rw [hR_map]
    _ = recovery (S.erasureChannelFromRegister rho.toOperator) := by
          rw [S.erasureKraus_inducedMap_eq_erasureChannelFromRegister]
    _ = rho.toOperator := hcorrect rho hRho
end QEC.Semantics.QuditSubsystem
