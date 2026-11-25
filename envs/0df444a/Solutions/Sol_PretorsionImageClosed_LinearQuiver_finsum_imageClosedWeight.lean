-- Prove2me | solution 1 for PretorsionImageClosed.LinearQuiver.finsum_imageClosedWeight
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T04:41:28.854714+00:00
-- url     : https://prove2.me/submissions/f530b43d-3e9f-4278-8862-c47a849ac024

module
public import Definitions.Def_PretorsionImageClosed_LinearQuiver_ImageClosed
public import Definitions.Def_PretorsionImageClosed_LinearQuiver_Counting
public import Definitions.Def_PretorsionImageClosed_Gandhi_Delta
public import Definitions.Def_PretorsionImageClosed_LinearQuiver_IntervalFamilies
public import Theorems.Thm_PretorsionImageClosed_LinearQuiver_imageClosedWeight_eq

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
theorem _root_.solution :
    ∑ᶠ Z : ImageClosedSubcategory k n, imageClosedWeight k n Z = ∑ D : ClosedFamily n, fWeight D := by
  rw [finsum_eq_sum_of_fintype, Finset.sum_congr rfl (fun Z _ => imageClosedWeight_eq Z)]
  exact Fintype.sum_equiv imageClosedEquiv _ _ (fun _ => rfl)
end PretorsionImageClosed.LinearQuiver
