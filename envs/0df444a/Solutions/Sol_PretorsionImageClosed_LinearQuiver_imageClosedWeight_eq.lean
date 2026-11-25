-- Prove2me | solution 1 for PretorsionImageClosed.LinearQuiver.imageClosedWeight_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T04:34:31.227102+00:00
-- url     : https://prove2.me/submissions/88488596-05b2-4090-af5b-cb0a3150bd29

module
public import Definitions.Def_PretorsionImageClosed_LinearQuiver_ImageClosed
public import Definitions.Def_PretorsionImageClosed_LinearQuiver_Counting
public import Definitions.Def_PretorsionImageClosed_Gandhi_Delta
public import Definitions.Def_PretorsionImageClosed_LinearQuiver_IntervalFamilies
public import Theorems.Thm_PretorsionImageClosed_LinearQuiver_rho_subcategory_family
public import Theorems.Thm_PretorsionImageClosed_LinearQuiver_indCard_subcategory_family

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
theorem _root_.solution (Z : ImageClosedSubcategory k n) :
    imageClosedWeight k n Z = fWeight (imageClosedEquiv Z) := by
  show X ^ rho Z.1.prop * C (q ^ indCard Z.1.prop) =
    X ^ (familyOf Z.1).lastCount * C (q ^ (familyOf Z.1).D.card)
  conv_lhs => rw [← subcategory_familyOf Z.1]
  rw [rho_subcategory_family, indCard_subcategory_family]
end PretorsionImageClosed.LinearQuiver
