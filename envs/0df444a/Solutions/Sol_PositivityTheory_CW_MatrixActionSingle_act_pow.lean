-- Prove2me | solution 1 for PositivityTheory.CW.MatrixActionSingle.act_pow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T11:28:29.267885+00:00
-- url     : https://prove2.me/submissions/6d2c7183-4d11-4570-93f6-cdca2249b0fc

import Definitions.Def_Development_WeilBound_CoreStatements_PublishedTheorems_CasselmanWallach_FunctionalCalculusLaws
import Definitions.Def_Development_WeilBound_CoreStatements_PublishedTheorems_CasselmanWallach_ColumnMomentsOfSymmetric
import Theorems.Thm_PositivityTheory_CW_MatrixActionSingle_act_apply
import Theorems.Thm_PositivityTheory_CW_MatrixActionSingle_act_mul

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
theorem _root_.solution (A : Matrix (Fin n) (Fin n) (Module.End ℂ V)) (m : ℕ) (u : PiLp 2 fun _ : Fin n => V) :
    act (A ^ m) u = (act A ^ m) u := by
  induction m generalizing u with
  | zero =>
    ext a
    simp [act_apply, Matrix.one_apply]
    rw [Finset.sum_eq_single a (fun b _ hb => by simp [Ne.symm hb]) (by simp)]
    simp
  | succ m ih => rw [pow_succ, act_mul, ih, pow_succ, Module.End.mul_apply]
end PositivityTheory.CW.MatrixActionSingle
