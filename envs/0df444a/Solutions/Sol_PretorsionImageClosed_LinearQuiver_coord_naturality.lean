-- Prove2me | solution 1 for PretorsionImageClosed.LinearQuiver.coord_naturality
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T03:04:40.654351+00:00
-- url     : https://prove2.me/submissions/1a2a49e2-8f60-46fa-b36f-c87f3a9cbe04

module
public import Definitions.Def_PretorsionImageClosed_LinearQuiver_Interval
public import Definitions.Def_PretorsionImageClosed_Subobjects_Preimage
public import Definitions.Def_PretorsionImageClosed_Length_Representations
public import Mathlib.CategoryTheory.Limits.FunctorCategory.EpiMono
public import Definitions.Def_PretorsionImageClosed_LinearQuiver_Hom
public import Theorems.Thm_PretorsionImageClosed_LinearQuiver_unit_val_of_mem
public import Theorems.Thm_PretorsionImageClosed_LinearQuiver_app_val

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
theorem _root_.solution {c d a b : Fin n} (η : interval k c d ⟶ interval k a b) {i j : Fin n}
    (hij : i ≤ j) (hi : c ≤ i ∧ i ≤ d) :
    (if j ≤ d then coord η j else 0) = if j ≤ b then coord η i else 0 := by
  have hnat := congrArg (fun g => (g.hom.hom (unit k c d i)).1) (η.naturality (homOfLE hij))
  change ((η.app j).hom.hom (((interval k c d).map (homOfLE hij)).hom.hom (unit k c d i))).1 =
    (((interval k a b).map (homOfLE hij)).hom.hom ((η.app i).hom.hom (unit k c d i))).1 at hnat
  -- left side: `η_j` of the structure map applied to the unit
  have hl : ((η.app j).hom.hom (((interval k c d).map (homOfLE hij)).hom.hom (unit k c d i))).1 =
      (if j ≤ d then (1 : k) else 0) * coord η j := by
    rw [app_val]
    congr 1
    change ((inclusionOrZero k _ _ (unit k c d i) : intervalSpace k c d j) : k) = _
    rw [coe_intervalMap k hij, unit_val_of_mem k hi]
  -- right side: the structure map of `η_i` of the unit
  have hr : (((interval k a b).map (homOfLE hij)).hom.hom ((η.app i).hom.hom (unit k c d i))).1 =
      if j ≤ b then coord η i else 0 := by
    change ((inclusionOrZero k _ _ _ : intervalSpace k a b j) : k) = _
    rw [coe_intervalMap k hij]
    rfl
  rw [hl, hr] at hnat
  rw [← hnat]
  by_cases hjd : j ≤ d
  · rw [if_pos hjd, if_pos hjd, one_mul]
  · rw [if_neg hjd, if_neg hjd, zero_mul]
end PretorsionImageClosed.LinearQuiver
