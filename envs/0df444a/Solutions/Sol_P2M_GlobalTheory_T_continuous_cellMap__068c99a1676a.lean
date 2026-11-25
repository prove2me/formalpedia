-- Prove2me | solution 1 for P2M_GlobalTheory_T_continuous_cellMap__068c99a1676a
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T02:33:40.49235+00:00
-- url     : https://prove2.me/submissions/91e664da-e6f1-4a91-988d-7e983165d3e9

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_ContinuousCellMap
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AutomorphicMembership_IsClosedFlagsIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_UniMatBlockTriangular
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_ContinuousCellMapStatement
import Theorems.Thm_GlobalTheory_FlagPts_continuous_cellMap


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
theorem _root_.solution : ∀ (k : Type) [Field k] (ι : Type) [Fintype ι] (V : ι → Type) [∀ i, AddCommGroup (V i)] [∀ i, Module k (V i)] [∀ i, FiniteDimensional k (V i)] (b : Frames k V), Continuous (cellMap b) := by
  first | exact @GlobalTheory.FlagPts.continuous_cellMap | exact GlobalTheory.FlagPts.continuous_cellMap | (intros; apply GlobalTheory.FlagPts.continuous_cellMap <;> assumption)
end _root_.GlobalTheory.T
