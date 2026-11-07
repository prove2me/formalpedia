-- Prove2me | solution 1 for QEC.Coding.why24ComputationalLabelEquiv_add
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T13:26:25.170193+00:00
-- url     : https://prove2.me/submissions/7377b81d-add3-4580-8b3c-4764b5ba063b

import Definitions.Def_QEC_Coding_Stabilizer_PauliSemantics
import Definitions.Def_QEC_Coding_QuditQubitConversion_SelfDualBasis
import Definitions.Def_QEC_Coding_QuditQubitConversion_Transport
import Theorems.Thm_QEC_Coding_why24ComputationalLabelEquiv_coordinates
import Theorems.Thm_QEC_Coding_f1024SelectedCoordinates_label_symm

set_option autoImplicit false
noncomputable section
open QEC QEC.Coding
open scoped BigOperators
namespace QEC.Coding
theorem _root_.solution (β : F1024)
    (bits : Semantics.Qubit.Bitstring (Fin 10)) :
    why24ComputationalLabelEquiv (why24ComputationalLabelEquiv.symm bits + β) =
      Semantics.Qubit.flipSupport (PauliSymplectic.binarySupport (f1024SelectedCoordinates β))
        bits := by
  apply (PauliSymplectic.bitstringWordEquiv (Fin 10)).injective
  calc
    PauliSymplectic.bitstringWordEquiv (Fin 10)
        (why24ComputationalLabelEquiv
          (why24ComputationalLabelEquiv.symm bits + β)) =
        f1024SelectedCoordinates (why24ComputationalLabelEquiv.symm bits + β) :=
      why24ComputationalLabelEquiv_coordinates _
    _ = f1024SelectedCoordinates (why24ComputationalLabelEquiv.symm bits) +
        f1024SelectedCoordinates β := by
      exact f1024SelectedCoordinates.map_add _ _
    _ = PauliSymplectic.bitstringWordEquiv (Fin 10) bits +
        f1024SelectedCoordinates β := by
      rw [f1024SelectedCoordinates_label_symm]
    _ = PauliSymplectic.bitstringWordEquiv (Fin 10)
        (Semantics.Qubit.flipSupport
          (PauliSymplectic.binarySupport (f1024SelectedCoordinates β)) bits) := by
      exact (PauliSymplectic.bitstringWordEquiv_flipSupport
        (f1024SelectedCoordinates β) bits).symm
end QEC.Coding
