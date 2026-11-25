-- Prove2me | solution 1 for PositivityTheory.CW.MatrixActionSingle.adjSign_symm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T11:32:46.924347+00:00
-- url     : https://prove2.me/submissions/caac208a-50d0-43e5-9aca-4a75a61409ac

import Definitions.Def_Development_WeilBound_CoreStatements_PublishedTheorems_CasselmanWallach_FunctionalCalculusLaws
import Definitions.Def_Development_WeilBound_CoreStatements_PublishedTheorems_CasselmanWallach_ColumnMomentsOfSymmetric

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix Finset ReciprocityTheory.ChartRestriction.DS
open PositivityTheory PositivityTheory.CW
open PositivityTheory.CW.MatrixActionSingle
variable {n : ℕ} {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
namespace PositivityTheory.CW.MatrixActionSingle
theorem _root_.solution (ε : Fin n → Bool) (a b : Fin n) : adjSign ε a b = adjSign ε b a := by
  simp [adjSign, eq_comm]
end PositivityTheory.CW.MatrixActionSingle
