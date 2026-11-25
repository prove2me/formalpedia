-- Prove2me | solution 1 for P2M_GlobalTheory_T_isOpenMap_cellMap__6da3daee2469
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T02:33:56.841222+00:00
-- url     : https://prove2.me/submissions/ba1c0a85-083b-4170-99e2-b355a7623ceb

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_IsOpenMapCellMap
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AutomorphicMembership_IsClosedFlagsIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_UniMatBlockTriangular
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_IsOpenMapCellMapStatement

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module TopologicalSpace GlobalTheory.FlagPts
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (k : Type) [Field k] (ι : Type) [Fintype ι] (V : ι → Type) [∀ i, AddCommGroup (V i)] [∀ i, Module k (V i)] [∀ i, FiniteDimensional k (V i)] (b : Frames k V), IsOpenMap (cellMap b) := by
  first | exact @GlobalTheory.FlagPts.isOpenMap_cellMap | exact GlobalTheory.FlagPts.isOpenMap_cellMap | (intros; apply GlobalTheory.FlagPts.isOpenMap_cellMap <;> assumption)
end _root_.GlobalTheory.T
