-- Prove2me | solution 1 for PretorsionImageClosed.LinearQuiver.restrict_glue
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T06:49:45.949019+00:00
-- url     : https://prove2.me/submissions/7ca7b5ad-8488-4371-8021-f3f5b64ac8bd

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
    (hC : Cont ⊆ candRows p) (hc : Allowed p Cont c) : (glue p Cont c hc).restrict = p := by
  apply Subtype.ext
  apply Prod.ext
  · apply RowCutoff.ext
    funext a
    show min ((glueRow p Cont).β a.castSucc) n = p.1.1.β a
    by_cases h : a.castSucc ∈ Cont
    · rw [glueRow_apply_of_mem h]
      have := mem_candRows.1 (hC h)
      rw [βext_castSucc] at this
      omega
    · rw [glueRow_apply_of_notMem h, βext_castSucc]
      exact min_eq_left (p.1.1.β_le a)
  · apply ColCutoff.ext
    funext d
    exact glueCol_castSucc p c d
end PretorsionImageClosed.LinearQuiver
