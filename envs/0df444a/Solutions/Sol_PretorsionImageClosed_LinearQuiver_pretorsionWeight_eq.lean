-- Prove2me | solution 1 for PretorsionImageClosed.LinearQuiver.pretorsionWeight_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T09:25:04.516738+00:00
-- url     : https://prove2.me/submissions/3b2913c5-7f12-49e9-86e1-994dbdab6b69

module
public import Definitions.Def_PretorsionImageClosed_LinearQuiver_CutoffCriterion
public import Definitions.Def_PretorsionImageClosed_LinearQuiver_Counting
public import Definitions.Def_PretorsionImageClosed_Gandhi_Delta
public import Definitions.Def_PretorsionImageClosed_LinearQuiver_CutoffWeights
public import Theorems.Thm_PretorsionImageClosed_LinearQuiver_rho_subcategory
public import Theorems.Thm_PretorsionImageClosed_LinearQuiver_indCard_inf
public import Theorems.Thm_PretorsionImageClosed_Statement_IsPretorsionTheory_isQuotientClosed
public import Theorems.Thm_PretorsionImageClosed_Statement_IsPretorsionTheory_isSubobjectClosed


set_option autoImplicit true
@[expose] public section
public section
set_option autoImplicit false
noncomputable section
open PretorsionImageClosed
open CategoryTheory Limits Statement Polynomial Finset
open PretorsionImageClosed.LinearQuiver
universe u
variable {k : Type u} [Field k] {n : ℕ}
namespace PretorsionImageClosed.LinearQuiver
theorem _root_.solution (P : PretorsionTheory (Statement.LinRep k n)) :
    pretorsionWeight k n P = cpWeight (pretorsionEquiv P) := by
  have hT := rowCutoff_subcategory P.isPretorsionTheory.isQuotientClosed
  have hF := colCutoff_subcategory P.isPretorsionTheory.isSubobjectClosed
  show X ^ rho P.T.prop * C (q ^ indCard (P.T.prop ⊓ P.F.prop)) =
    X ^ (rowCutoff P.T).rowsReaching * C (q ^ middleCount (rowCutoff P.T) (colCutoff P.F))
  rw [← rho_subcategory (k := k), ← indCard_inf (k := k), hT, hF]
end PretorsionImageClosed.LinearQuiver
