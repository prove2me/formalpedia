-- Prove2me | solution 1 for PretorsionImageClosed.LinearQuiver.prop_cokernel_suffix_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T03:34:18.494797+00:00
-- url     : https://prove2.me/submissions/a3baa18d-ea0b-463f-94aa-3f1b619c2bb8

module
public import Definitions.Def_PretorsionImageClosed_LinearQuiver_ImageClosed
public import Definitions.Def_PretorsionImageClosed_Subobjects_Quotients
public import Definitions.Def_PretorsionImageClosed_Pretorsion_Criterion
public import Definitions.Def_PretorsionImageClosed_LinearQuiver_IntervalTraceReject
public import Theorems.Thm_PretorsionImageClosed_Statement_Subcategory_prop_iff_of_iso


set_option autoImplicit true
@[expose] public section
public section
set_option autoImplicit false
noncomputable section
open PretorsionImageClosed
open CategoryTheory Limits Statement Subcategory
open PretorsionImageClosed.LinearQuiver
universe u
variable {k : Type u} [Field k] {n : ℕ}
namespace PretorsionImageClosed.LinearQuiver
theorem _root_.solution (Z : Subcategory (Statement.LinRep k n)) {c ℓ d v : Fin n}
    (hℓd : ℓ ≤ d) (hcv : c ≤ v) (hv : ℓ.val + 1 = v.val) :
    Z.prop (cokernel (suffix (k := k) c d v hcv).arrow) ↔ Z.prop (interval k c ℓ) :=
  Z.prop_iff_of_iso (cokernelSuffixIso hℓd hcv hv)
end PretorsionImageClosed.LinearQuiver
