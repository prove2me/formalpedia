-- Prove2me | solution 1 for PretorsionImageClosed.LinearQuiver.coord_eq_coord_mul_canonical
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T03:08:57.549044+00:00
-- url     : https://prove2.me/submissions/45b04c89-a015-4424-900a-71eee1a68517

module
public import Definitions.Def_PretorsionImageClosed_LinearQuiver_Interval
public import Definitions.Def_PretorsionImageClosed_Subobjects_Preimage
public import Definitions.Def_PretorsionImageClosed_Length_Representations
public import Mathlib.CategoryTheory.Limits.FunctorCategory.EpiMono
public import Definitions.Def_PretorsionImageClosed_LinearQuiver_Hom
public import Theorems.Thm_PretorsionImageClosed_LinearQuiver_coord_eq_zero_of_not_mem_src
public import Theorems.Thm_PretorsionImageClosed_LinearQuiver_coord_eq_zero_of_not_mem_tgt
public import Theorems.Thm_PretorsionImageClosed_LinearQuiver_coord_eq_coord
public import Theorems.Thm_PretorsionImageClosed_LinearQuiver_coord_canonicalHom

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
theorem _root_.solution {c d a b : Fin n} (η : interval k c d ⟶ interval k a b)
    (hac : a ≤ c) (hbd : b ≤ d) (i : Fin n) :
    coord η i = coord η c * coord (canonicalHom (k := k) hac hbd) i := by
  rw [coord_canonicalHom]
  by_cases hi : c ≤ i ∧ i ≤ b
  · rw [if_pos hi, mul_one]
    exact coord_eq_coord η hbd hi.1 le_rfl hi.2
  · rw [if_neg hi, mul_zero]
    by_cases hi' : c ≤ i ∧ i ≤ d
    · exact coord_eq_zero_of_not_mem_tgt η (fun h => hi ⟨hi'.1, h.2⟩)
    · exact coord_eq_zero_of_not_mem_src η hi'
end PretorsionImageClosed.LinearQuiver
