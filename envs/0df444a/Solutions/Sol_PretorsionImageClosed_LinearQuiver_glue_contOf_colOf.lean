-- Prove2me | solution 1 for PretorsionImageClosed.LinearQuiver.glue_contOf_colOf
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T06:51:15.754661+00:00
-- url     : https://prove2.me/submissions/b3046d8e-e8c8-4897-a365-ec427918be11

module
public import Definitions.Def_PretorsionImageClosed_LinearQuiver_CutoffWeights
public import Definitions.Def_PretorsionImageClosed_Gandhi_ColumnSum
public import Definitions.Def_PretorsionImageClosed_LinearQuiver_CutoffRestriction
public import Theorems.Thm_PretorsionImageClosed_LinearQuiver_colValue_colOf
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
theorem _root_.solution (x : CutoffPair (n + 1)) :
    glue x.restrict (contOf x) (colOf x) (allowed_colOf x) = x := by
  apply Subtype.ext
  apply Prod.ext
  · apply RowCutoff.ext
    funext a
    show (if a ∈ contOf x then n + 1 else βext x.restrict a) = x.1.1.β a
    by_cases h : a ∈ contOf x
    · rw [if_pos h]
      exact (mem_contOf.1 h).symm
    · rw [if_neg h, βext_restrict]
      have h1 := x.1.1.β_le a
      have h2 : x.1.1.β a ≠ n + 1 := fun h' => h (mem_contOf.2 h')
      omega
  · apply ColCutoff.ext
    funext d
    induction d using Fin.lastCases with
    | last => exact (glueCol_last _ _).trans (colValue_colOf x)
    | cast d => exact glueCol_castSucc _ _ d
end PretorsionImageClosed.LinearQuiver
