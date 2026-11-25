-- Prove2me | solution 1 for PretorsionImageClosed.LinearQuiver.coord_eq_coord
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T03:07:54.473991+00:00
-- url     : https://prove2.me/submissions/e323341d-0d3e-4ebc-9ffd-60a56c372556

module
public import Definitions.Def_PretorsionImageClosed_LinearQuiver_Interval
public import Definitions.Def_PretorsionImageClosed_Subobjects_Preimage
public import Definitions.Def_PretorsionImageClosed_Length_Representations
public import Mathlib.CategoryTheory.Limits.FunctorCategory.EpiMono
public import Definitions.Def_PretorsionImageClosed_LinearQuiver_Hom
public import Theorems.Thm_PretorsionImageClosed_LinearQuiver_coord_naturality

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
theorem _root_.solution {c d a b : Fin n} (η : interval k c d ⟶ interval k a b) (hbd : b ≤ d)
    {i j : Fin n} (hij : i ≤ j) (hi : c ≤ i) (hj : j ≤ b) : coord η j = coord η i := by
  have := coord_naturality η hij ⟨hi, (hij.trans hj).trans hbd⟩
  rwa [if_pos (hj.trans hbd), if_pos hj] at this
end PretorsionImageClosed.LinearQuiver
