-- Prove2me | solution 1 for PretorsionImageClosed.LinearQuiver.colCount_glue_last
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T06:50:35.351608+00:00
-- url     : https://prove2.me/submissions/013bf3dd-9275-479e-b602-4c562e60b967

module
public import Definitions.Def_PretorsionImageClosed_LinearQuiver_CutoffWeights
public import Definitions.Def_PretorsionImageClosed_Gandhi_ColumnSum
public import Definitions.Def_PretorsionImageClosed_LinearQuiver_CutoffRestriction
public import Theorems.Thm_PretorsionImageClosed_LinearQuiver_lt_glueRow_iff
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
theorem _root_.solution (p : CutoffPair n) (Cont : Finset (Fin (n + 1))) (c : Option (Fin (n + 1))) :
    colCount (glueRow p Cont) (glueCol p c) (Fin.last n) =
      (Cont.filter (fun a => colValue c ≤ a.val)).card := by
  unfold colCount
  congr 1
  ext a
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Fin.le_last, Fin.val_last, glueCol_last,
    lt_glueRow_iff]
end PretorsionImageClosed.LinearQuiver
