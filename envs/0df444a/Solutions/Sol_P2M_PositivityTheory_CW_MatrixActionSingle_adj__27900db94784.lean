-- Prove2me | solution 1 for P2M_PositivityTheory_CW_MatrixActionSingle_adj__27900db94784
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T11:48:21.33854+00:00
-- url     : https://prove2.me/submissions/21ad28ac-8605-40cc-84b5-7f87893c499b

import Definitions.Def_Development_WeilBound_CoreStatements_PublishedTheorems_CasselmanWallach_FunctionalCalculusLaws
import Definitions.Def_Development_WeilBound_CoreStatements_PublishedTheorems_CasselmanWallach_ColumnMomentsOfSymmetric
import Theorems.Thm_PositivityTheory_CW_MatrixActionSingle_adj

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
theorem _root_.solution (ε : Fin n → Bool) (E : Fin n → Fin n → Module.End ℂ V) (hu : IsInfUnitary ε E)
    (u w : PiLp 2 fun _ : Fin n => V) :
    inner ℂ (act (Md ε E) u) w = inner ℂ u (act (Mm E) w) := by
  rw [← inner_conj_symm, ← adj ε E hu, inner_conj_symm]
end PositivityTheory.CW.MatrixActionSingle
