-- Prove2me | solution 1 for QEC.Locality.wordPauli_contribution_matrix_element
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T13:51:42.556492+00:00
-- url     : https://prove2.me/submissions/3660abf9-261a-4625-9581-d4dae955cef7

import Definitions.Def_QEC_Semantics_Core_Subsystem
import Definitions.Def_QEC_Coding_Stabilizer_PauliSemantics
import Definitions.Def_QEC_Locality_CorrectableRegions_LocalPauliErasureTransfer
import Theorems.Thm_QEC_Locality_wordPauliOperatorFactorized_adjoint_apply_tmul
import Theorems.Thm_QEC_Locality_wordPauli_phase_product

set_option autoImplicit false
open QEC QEC.Locality
open scoped TensorProduct BigOperators
open QEC Semantics
open Coding
universe u v
variable {ι : Type u} [Fintype ι] [DecidableEq ι]
namespace QEC.Locality
theorem _root_.solution (S : FiniteSubsystem ι)
    (p : LocalPauliWordIndex S) (A : Operator S.factorizedSystem)
    (a b : Qubit.Bitstring S.SelectedCoordinates)
    (k l : S.complementSystem) :
    inner Complex (ket b ⊗ₜ[Complex] l)
      (((wordPauliOperatorFactorized S p).comp
        (A.comp (LinearMap.adjoint (wordPauliOperatorFactorized S p))))
        (ket a ⊗ₜ[Complex] k)) =
      (PauliSymplectic.binaryPhaseScalar
        (Coding.wordPairing (F := ZMod 2) (ι := S.SelectedCoordinates) p.2
          ((PauliSymplectic.bitstringWordEquiv _ b) +
            PauliSymplectic.bitstringWordEquiv _ a))) *
        inner Complex
          (ket (Qubit.flipSupport (PauliSymplectic.binarySupport p.1) b) ⊗ₜ[Complex] l)
          (A (ket (Qubit.flipSupport (PauliSymplectic.binarySupport p.1) a) ⊗ₜ[Complex] k)) := by
  change inner Complex (ket b ⊗ₜ[Complex] l)
    (wordPauliOperatorFactorized S p
      (A ((LinearMap.adjoint (wordPauliOperatorFactorized S p))
        (ket a ⊗ₜ[Complex] k)))) = _
  rw [← LinearMap.adjoint_inner_left]
  rw [wordPauliOperatorFactorized_adjoint_apply_tmul,
    wordPauliOperatorFactorized_adjoint_apply_tmul]
  rw [map_smul]
  change inner Complex
    (Qubit.zSupportPhase (PauliSymplectic.binarySupport p.2)
      (Qubit.flipSupport (PauliSymplectic.binarySupport p.1) b) •
        (ket (Qubit.flipSupport (PauliSymplectic.binarySupport p.1) b) ⊗ₜ[Complex] l))
    (Qubit.zSupportPhase (PauliSymplectic.binarySupport p.2)
      (Qubit.flipSupport (PauliSymplectic.binarySupport p.1) a) •
        A (ket (Qubit.flipSupport (PauliSymplectic.binarySupport p.1) a) ⊗ₜ[Complex] k)) = _
  rw [inner_smul_left (ket (Qubit.flipSupport (PauliSymplectic.binarySupport p.1) b) ⊗ₜ[Complex] l)
    _ (Qubit.zSupportPhase (PauliSymplectic.binarySupport p.2)
      (Qubit.flipSupport (PauliSymplectic.binarySupport p.1) b))]
  rw [inner_smul_right
    (ket (Qubit.flipSupport (PauliSymplectic.binarySupport p.1) b) ⊗ₜ[Complex] l)
    (A (ket (Qubit.flipSupport (PauliSymplectic.binarySupport p.1) a) ⊗ₜ[Complex] k))
    (Qubit.zSupportPhase (PauliSymplectic.binarySupport p.2)
      (Qubit.flipSupport (PauliSymplectic.binarySupport p.1) a))]
  change star (Qubit.zSupportPhase (PauliSymplectic.binarySupport p.2)
      (Qubit.flipSupport (PauliSymplectic.binarySupport p.1) b)) *
    (Qubit.zSupportPhase (PauliSymplectic.binarySupport p.2)
      (Qubit.flipSupport (PauliSymplectic.binarySupport p.1) a) * _) = _
  rw [← mul_assoc]
  rw [wordPauli_phase_product]
end QEC.Locality
