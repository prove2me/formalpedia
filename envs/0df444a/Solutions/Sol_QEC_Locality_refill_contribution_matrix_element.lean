-- Prove2me | solution 1 for QEC.Locality.refill_contribution_matrix_element
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T13:47:01.409711+00:00
-- url     : https://prove2.me/submissions/2158d03b-13de-44c5-b263-80c6a23c413f

import Definitions.Def_QEC_Semantics_Core_Subsystem
import Definitions.Def_QEC_Coding_Stabilizer_PauliSemantics
import Definitions.Def_QEC_Locality_CorrectableRegions_LocalPauliErasureTransfer

set_option autoImplicit false
open QEC QEC.Locality
open scoped TensorProduct BigOperators
open QEC Semantics
open Coding
universe u v
variable {ι : Type u} [Fintype ι] [DecidableEq ι]
namespace QEC.Locality
theorem _root_.solution (S : FiniteSubsystem ι)
    (r : Qubit.Bitstring S.SelectedCoordinates)
    (B : Operator S.complementSystem)
    (a b : Qubit.Bitstring S.SelectedCoordinates)
    (k l : S.complementSystem) :
    inner Complex (ket b ⊗ₜ[Complex] l)
      ((tensorLeft S.selectedSystem S.complementSystem (ket r)).comp
        (B.comp (LinearMap.adjoint
          (tensorLeft S.selectedSystem S.complementSystem (ket r))))
        (ket a ⊗ₜ[Complex] k)) =
      inner Complex (ket b) (ket r) * inner Complex (ket r) (ket a) *
        inner Complex l (B k) := by
  change inner Complex (ket b ⊗ₜ[Complex] l)
    (tensorLeft S.selectedSystem S.complementSystem (ket r)
      (B ((LinearMap.adjoint
        (tensorLeft S.selectedSystem S.complementSystem (ket r)))
        (ket a ⊗ₜ[Complex] k)))) = _
  rw [tensorLeft_adjoint_tmul, map_smul, map_smul]
  change inner Complex (ket b ⊗ₜ[Complex] l)
    (inner Complex (ket r) (ket a) • (ket r ⊗ₜ[Complex] B k)) = _
  rw [inner_smul_right (ket b ⊗ₜ[Complex] l) (ket r ⊗ₜ[Complex] B k)
    (inner Complex (ket r) (ket a)), TensorProduct.inner_tmul]
  ring
end QEC.Locality
