-- Prove2me | solution 1 for PretorsionImageClosed.LinearQuiver.ClosedFamily.restrict_glue
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T04:22:36.268853+00:00
-- url     : https://prove2.me/submissions/6ab68fea-5b4c-4f41-983b-19841ec15fe2

module
public import Definitions.Def_PretorsionImageClosed_LinearQuiver_IntervalFamilies
public import Definitions.Def_PretorsionImageClosed_Gandhi_ColumnSum
public import Definitions.Def_PretorsionImageClosed_LinearQuiver_FamilyRestriction
public import Theorems.Thm_PretorsionImageClosed_LinearQuiver_IntervalFamily_restrict_glue
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
namespace ClosedFamily
theorem _root_.solution (D : ClosedFamily n) (J : Finset (Fin (n + 1))) (hJ : J ⊆ adm D.1) :
    (D.glue J hJ).restrict = D :=
  Subtype.ext (IntervalFamily.restrict_glue D.1 J)
end ClosedFamily
end PretorsionImageClosed.LinearQuiver
