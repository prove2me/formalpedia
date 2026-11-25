-- Prove2me | solution 1 for PretorsionImageClosed.LinearQuiver.middleCount_glue
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T06:52:05.679167+00:00
-- url     : https://prove2.me/submissions/8d88f76c-dadf-43c1-b2bd-747cdeec7337

module
public import Definitions.Def_PretorsionImageClosed_LinearQuiver_CutoffWeights
public import Definitions.Def_PretorsionImageClosed_Gandhi_ColumnSum
public import Definitions.Def_PretorsionImageClosed_LinearQuiver_CutoffRestriction
public import Theorems.Thm_PretorsionImageClosed_LinearQuiver_colCount_glue_castSucc
public import Theorems.Thm_PretorsionImageClosed_LinearQuiver_colCount_glue_last

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
    (hC : Cont ⊆ candRows p) :
    middleCount (glueRow p Cont) (glueCol p c) =
      middleCount p.1.1 p.1.2 + (Cont.filter (fun a => colValue c ≤ a.val)).card := by
  unfold middleCount
  rw [Fin.sum_univ_castSucc, colCount_glue_last]
  congr 1
  exact Finset.sum_congr rfl (fun d _ => colCount_glue_castSucc p Cont c hC d)
end PretorsionImageClosed.LinearQuiver
