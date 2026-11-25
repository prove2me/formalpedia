-- Prove2me | solution 1 for PositivityTheory.CW.MatrixActionSingle.act_single
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T11:32:43.652725+00:00
-- url     : https://prove2.me/submissions/cc2c816e-f5aa-485d-add3-cfe842c0e34d

import Definitions.Def_Development_WeilBound_CoreStatements_PublishedTheorems_CasselmanWallach_FunctionalCalculusLaws
import Definitions.Def_Development_WeilBound_CoreStatements_PublishedTheorems_CasselmanWallach_ColumnMomentsOfSymmetric
import Theorems.Thm_PositivityTheory_CW_MatrixActionSingle_act_apply

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
theorem _root_.solution (A : Matrix (Fin n) (Fin n) (Module.End ℂ V)) (e a : Fin n) (v : V) :
    act A (PiLp.single 2 e v) a = A a e v := by
  rw [act_apply, Finset.sum_eq_single e]
  · simp [PiLp.single_apply]
  · intro b _ hb
    simp [PiLp.single_apply, hb]
  · intro h
    exact absurd (Finset.mem_univ e) h
end PositivityTheory.CW.MatrixActionSingle
