-- Prove2me | solution 1 for PretorsionImageClosed.LinearQuiver.colOf_glue
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T06:50:03.219137+00:00
-- url     : https://prove2.me/submissions/b1bdc068-8b80-4fe2-bcd3-5ce76718bfcc

module
public import Definitions.Def_PretorsionImageClosed_LinearQuiver_CutoffWeights
public import Definitions.Def_PretorsionImageClosed_Gandhi_ColumnSum
public import Definitions.Def_PretorsionImageClosed_LinearQuiver_CutoffRestriction
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
theorem _root_.solution (p : CutoffPair n) (Cont : Finset (Fin (n + 1))) (c : Option (Fin (n + 1)))
    (hc : Allowed p Cont c) : colOf (glue p Cont c hc) = c := by
  unfold colOf
  have hcol : (glue p Cont c hc).1.2.α (Fin.last n) = colValue c := glueCol_last p c
  cases c with
  | none => simp [hcol, colValue]
  | some e =>
    rw [dif_neg (by rw [hcol]; simp [colValue])]
    congr 1
    apply Fin.ext
    simp [hcol, colValue]
end PretorsionImageClosed.LinearQuiver
