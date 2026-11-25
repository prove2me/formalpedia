-- Prove2me | solution 1 for PositivityTheory.CW.MatrixActionSingle.inner_single
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T11:29:33.532943+00:00
-- url     : https://prove2.me/submissions/5d06f48a-3158-4677-b716-f95791a966d9

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
theorem _root_.solution (e : Fin n) (v : V) (w : PiLp 2 fun _ : Fin n => V) :
    inner ℂ (PiLp.single 2 e v) w = inner ℂ v (w e) := by
  rw [PiLp.inner_apply, Finset.sum_eq_single e (fun b _ hb => by simp [hb]) (by simp)]
  simp
end PositivityTheory.CW.MatrixActionSingle
