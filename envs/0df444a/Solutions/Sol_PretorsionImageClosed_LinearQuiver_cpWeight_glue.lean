-- Prove2me | solution 1 for PretorsionImageClosed.LinearQuiver.cpWeight_glue
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T06:53:25.309599+00:00
-- url     : https://prove2.me/submissions/d135ba5f-d093-4f91-84f6-f8189954dedf

module
public import Definitions.Def_PretorsionImageClosed_LinearQuiver_CutoffWeights
public import Definitions.Def_PretorsionImageClosed_Gandhi_ColumnSum
public import Definitions.Def_PretorsionImageClosed_LinearQuiver_CutoffRestriction
public import Theorems.Thm_PretorsionImageClosed_LinearQuiver_rowsReaching_glueRow
public import Theorems.Thm_PretorsionImageClosed_LinearQuiver_middleCount_glue

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
theorem _root_.solution (p : CutoffPair n) (Cont : Finset (Fin (n + 1))) (c : Option (Fin (n + 1)))
    (hC : Cont ⊆ candRows p) (hc : Allowed p Cont c) :
    cpWeight (glue p Cont c hc) = C (q ^ middleCount p.1.1 p.1.2) *
      (X ^ Cont.card * C (q ^ (Cont.filter (fun a => colValue c ≤ a.val)).card)) := by
  show X ^ (glueRow p Cont).rowsReaching * C (q ^ middleCount (glueRow p Cont) (glueCol p c)) = _
  rw [rowsReaching_glueRow, middleCount_glue p Cont c hC, pow_add, map_mul]
  ring
end PretorsionImageClosed.LinearQuiver
