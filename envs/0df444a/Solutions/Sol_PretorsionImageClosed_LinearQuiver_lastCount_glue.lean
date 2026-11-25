-- Prove2me | solution 1 for PretorsionImageClosed.LinearQuiver.lastCount_glue
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T04:23:09.076926+00:00
-- url     : https://prove2.me/submissions/4f09414a-4c45-4649-8c37-3daf6baf2f0f

module
public import Definitions.Def_PretorsionImageClosed_LinearQuiver_IntervalFamilies
public import Definitions.Def_PretorsionImageClosed_Gandhi_ColumnSum
public import Definitions.Def_PretorsionImageClosed_LinearQuiver_FamilyRestriction
public import Theorems.Thm_PretorsionImageClosed_LinearQuiver_lastCount_succ
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
theorem _root_.solution (D : IntervalFamily n) (J : Finset (Fin (n + 1))) :
    (D.glue J).lastCount = J.card := by
  rw [lastCount_succ]
  congr 1
  ext a
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, mem_glue_last]
end PretorsionImageClosed.LinearQuiver
