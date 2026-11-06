-- Prove2me | solution 1 for QEC.Locality.factorizedBasis_apply
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T13:46:42.444203+00:00
-- url     : https://prove2.me/submissions/ec837ee2-d54e-4d90-be24-7e73baf51bff

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
    (p : Qubit.Bitstring S.SelectedCoordinates × Qubit.Bitstring S.ComplementCoordinates) :
    factorizedBasis S p = ket p.1 ⊗ₜ[Complex] ket p.2 := by
  unfold factorizedBasis ket
  rw [OrthonormalBasis.tensorProduct_apply']
end QEC.Locality
