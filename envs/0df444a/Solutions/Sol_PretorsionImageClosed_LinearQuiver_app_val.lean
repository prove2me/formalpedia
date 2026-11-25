-- Prove2me | solution 1 for PretorsionImageClosed.LinearQuiver.app_val
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T03:03:40.208928+00:00
-- url     : https://prove2.me/submissions/5c17fbed-e3eb-4032-a44f-374e8831e0a9

module
public import Definitions.Def_PretorsionImageClosed_LinearQuiver_Interval
public import Definitions.Def_PretorsionImageClosed_Subobjects_Preimage
public import Definitions.Def_PretorsionImageClosed_Length_Representations
public import Mathlib.CategoryTheory.Limits.FunctorCategory.EpiMono
public import Definitions.Def_PretorsionImageClosed_LinearQuiver_Hom
public import Theorems.Thm_PretorsionImageClosed_LinearQuiver_eq_smul_unit

set_option autoImplicit true
@[expose] public section
public section
set_option autoImplicit false
noncomputable section
open PretorsionImageClosed
open CategoryTheory Limits
open PretorsionImageClosed.LinearQuiver
universe u
variable (k : Type u) [Field k] {n : ℕ}
variable {k}
namespace PretorsionImageClosed.LinearQuiver
theorem _root_.solution {c d a b : Fin n} (η : interval k c d ⟶ interval k a b) (i : Fin n)
    (x : intervalSpace k c d i) :
    ((η.app i).hom.hom x).1 = (x : k) * coord η i := by
  have h := congrArg (fun y => ((η.app i).hom.hom y).1) (eq_smul_unit k x)
  rw [h]
  erw [map_smul]
  rfl
end PretorsionImageClosed.LinearQuiver
