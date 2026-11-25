-- Prove2me | solution 1 for PretorsionImageClosed.LinearQuiver.ClosedFamily.glue_JOf
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T04:34:09.208861+00:00
-- url     : https://prove2.me/submissions/770c2065-4af6-44b1-80b2-396d2cbc4dd7

module
public import Definitions.Def_PretorsionImageClosed_LinearQuiver_IntervalFamilies
public import Definitions.Def_PretorsionImageClosed_Gandhi_ColumnSum
public import Definitions.Def_PretorsionImageClosed_LinearQuiver_FamilyRestriction
public import Theorems.Thm_PretorsionImageClosed_LinearQuiver_IntervalFamily_glue_JOf
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
theorem _root_.solution (D : ClosedFamily (n + 1)) :
    D.restrict.glue (JOf D.1) (JOf_subset_adm D.2) = D :=
  Subtype.ext (IntervalFamily.glue_JOf D.1)
end ClosedFamily
end PretorsionImageClosed.LinearQuiver
