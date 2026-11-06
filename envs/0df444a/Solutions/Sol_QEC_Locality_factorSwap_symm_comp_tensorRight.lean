-- Prove2me | solution 1 for QEC.Locality.factorSwap_symm_comp_tensorRight
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T12:38:41.761949+00:00
-- url     : https://prove2.me/submissions/d22cc96d-ccce-4bad-aa30-48f9a5d137a9

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
    (h : Qubit.Bitstring S.SelectedCoordinates) :
    S.factorSwap.symm.toLinearEquiv.toLinearMap.comp
      (tensorRight S.complementSystem S.selectedSystem (ket h)) =
      tensorLeft S.selectedSystem S.complementSystem (ket h) := by
  apply LinearMap.ext
  intro k
  rfl
end QEC.Locality
