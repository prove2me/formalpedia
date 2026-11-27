-- Prove2me | solution 1 for PositivityTheory.Mirab.Dim.index_uniSub
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-27T04:40:11.582115+00:00
-- url     : https://prove2.me/submissions/9b2e5a9b-d197-44f7-9f23-a5c9754ff4a9

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_PublishedFoundations_BlockTriangularOfSubOne
import Definitions.Def_Formalism_MirabolicMackeyTheory_MirabolicIsMackey
import Definitions.Def_Development_WeilBound_CoreStatements_RegularisedThetaMirabolic_CuspidalMirabolic_IndDim
import Theorems.Thm_Formalism_L2_Indef_Tree_index_Uv
import Theorems.Thm_Formalism_L2_Indef_Tree_mirab_levelGroups


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory.FiniteGL Formalism.L2.Indef.Tree Formalism.EigenvalueLevelCeiling
open PositivityTheory PositivityTheory.Mirab PositivityTheory.Mirab.Dim
variable {k : Type} [Field k] [Fintype k] (n : ℕ)
namespace PositivityTheory.Mirab.Dim
theorem _root_.solution : (uniSub k n).index = ∏ i ∈ Finset.Ico 1 (n + 1), (Fintype.card k ^ i - 1) :=
  index_Uv (kf := fun _ : Unit => k) (mirab_levelGroups (fun _ : Unit => k) n) ()
end PositivityTheory.Mirab.Dim
