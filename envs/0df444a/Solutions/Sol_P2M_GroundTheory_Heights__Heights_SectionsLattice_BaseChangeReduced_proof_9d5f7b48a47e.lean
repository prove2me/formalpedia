-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_SectionsLattice_BaseChangeReduced_proof_9d5f7b48a47e
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-27T05:09:08.13485+00:00
-- url     : https://prove2.me/submissions/c8ff2444-0bae-4379-83ee-9c63a30ed423

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ReducedTensors_Imports
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ReducedTensors_PBaseChangeReduced
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_SectionsLattice_BaseChangeReduced_isReduced_tensor_of_forall_finite_f9cc805ff916
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_SectionsLattice_BaseChangeReduced_isReduced_tensor_finite_finite_a8c992f86040

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open TensorProduct
open GroundTheory.Heights₂.Heights.SectionsLattice
open GroundTheory.Heights₂.Heights.SectionsLattice.BaseChangeReduced
namespace GroundTheory.Heights₂.Heights.SectionsLattice.BaseChangeReduced
theorem _root_.solution : BaseChangeReduced.Statement := by
  intro k L A _ _ _ _ _ _ hA
  have step : ∀ (E' : Type) [Field E'] [Algebra k E'] [FiniteDimensional k E'] (A' : Type)
      [CommRing A'] [Algebra k A'] [IsReduced A'], IsReduced (E' ⊗[k] A') :=
    fun E' _ _ _ A' _ _ _ =>
      isReduced_tensor_of_forall_finite (B := E') (fun E _ _ _ => isReduced_tensor_finite_finite E E') A'
  exact isReduced_tensor_of_forall_finite (B := L) (fun E _ _ _ => step E L) A
end GroundTheory.Heights₂.Heights.SectionsLattice.BaseChangeReduced
