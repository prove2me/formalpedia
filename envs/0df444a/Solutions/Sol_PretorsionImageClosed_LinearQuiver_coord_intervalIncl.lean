-- Prove2me | solution 1 for PretorsionImageClosed.LinearQuiver.coord_intervalIncl
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T03:08:34.820051+00:00
-- url     : https://prove2.me/submissions/94bac96b-60af-4c58-8a27-3b8c2094b414

module
public import Definitions.Def_PretorsionImageClosed_LinearQuiver_Indecomposables
public import Definitions.Def_PretorsionImageClosed_Subcategories_Trace
public import Definitions.Def_PretorsionImageClosed_LinearQuiver_Subobjects
public import Theorems.Thm_PretorsionImageClosed_LinearQuiver_unit_val


set_option autoImplicit true
@[expose] public section
public section
set_option autoImplicit false
noncomputable section
open PretorsionImageClosed
open CategoryTheory Limits Statement
open PretorsionImageClosed.LinearQuiver
universe u
variable {k : Type u} [Field k] {n : ℕ}
namespace PretorsionImageClosed.LinearQuiver
theorem _root_.solution {a ℓ d : Fin n} (h : a ≤ ℓ) (i : Fin n) :
    coord (intervalIncl k d h) i = if ℓ ≤ i ∧ i ≤ d then 1 else 0 := by
  unfold coord
  change ((inclusionOrZero k (intervalSpace k ℓ d i) (intervalSpace k a d i) (unit k ℓ d i) :
    intervalSpace k a d i) : k) = _
  rw [coe_inclusionOrZero_left k h, unit_val]
end PretorsionImageClosed.LinearQuiver
