-- Prove2me | solution 1 for QEC.Locality.binarySupport_embedSelectedWord_subset
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T16:41:02.314618+00:00
-- url     : https://prove2.me/submissions/a20ebf5b-2265-4d5f-8466-4eb5962944e3

import Definitions.Def_QEC_Coding_Stabilizer_Correctability
import Definitions.Def_QEC_Coding_Stabilizer_Distance
import Definitions.Def_QEC_Locality_CorrectableRegions_LocalPauliErasureTransfer
import Definitions.Def_QEC_Locality_CorrectableRegions_SemanticDistanceErasure

set_option autoImplicit false
noncomputable section
open QEC
open QEC.Locality
open QEC Semantics Coding
open scoped TensorProduct
open PauliSymplectic
universe u
variable {ι : Type u} [Fintype ι] [DecidableEq ι]
namespace QEC.Locality
theorem _root_.solution (S : FiniteSubsystem ι)
    (w : Coding.Word (ZMod 2) S.SelectedCoordinates) :
    binarySupport (embedSelectedWord S w) ⊆ S.selected := by
  intro i hi
  by_contra hnot
  have hzero : embedSelectedWord S w i = 0 :=
    embedSelectedWord_apply_not_mem S w hnot
  exact ((mem_binarySupport (embedSelectedWord S w) i).1 hi) hzero
end QEC.Locality
