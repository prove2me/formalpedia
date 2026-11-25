-- Prove2me | solution 1 for PretorsionImageClosed.LinearQuiver.contOf_glue
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T06:49:59.811934+00:00
-- url     : https://prove2.me/submissions/82852586-7f79-4074-adcb-09f9c80b2960

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
theorem _root_.solution (p : CutoffPair n) (Cont : Finset (Fin (n + 1))) (c : Option (Fin (n + 1)))
    (hc : Allowed p Cont c) : contOf (glue p Cont c hc) = Cont := by
  ext a
  rw [mem_contOf]
  exact glueRow_eq_succ_iff
end PretorsionImageClosed.LinearQuiver
