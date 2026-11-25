-- Prove2me | solution 1 for PretorsionImageClosed.LinearQuiver.rowsReaching_glueRow
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T06:51:13.166559+00:00
-- url     : https://prove2.me/submissions/a9c8a157-8697-4c1e-ba91-89823e9ffaa2

module
public import Definitions.Def_PretorsionImageClosed_LinearQuiver_CutoffWeights
public import Definitions.Def_PretorsionImageClosed_Gandhi_ColumnSum
public import Definitions.Def_PretorsionImageClosed_LinearQuiver_CutoffRestriction
public import Theorems.Thm_PretorsionImageClosed_LinearQuiver_glueRow_eq_succ_iff
public import Theorems.Thm_PretorsionImageClosed_Statement_PretorsionTheory_ext


set_option autoImplicit true
@[expose] public section
public section
set_option autoImplicit false
noncomputable section
open PretorsionImageClosed
open Statement Polynomial Finset
open PretorsionImageClosed.LinearQuiver
variable {n : ℕ}
namespace PretorsionImageClosed.LinearQuiver
theorem _root_.solution (p : CutoffPair n) (Cont : Finset (Fin (n + 1))) :
    (glueRow p Cont).rowsReaching = Cont.card := by
  unfold RowCutoff.rowsReaching
  rw [show univ.filter (fun a => (glueRow p Cont).β a = n + 1) = Cont from by
    ext a
    simp [glueRow_eq_succ_iff]]
end PretorsionImageClosed.LinearQuiver
