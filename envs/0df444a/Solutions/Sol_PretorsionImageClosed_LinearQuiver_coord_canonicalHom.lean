-- Prove2me | solution 1 for PretorsionImageClosed.LinearQuiver.coord_canonicalHom
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T01:23:58.551423+00:00
-- url     : https://prove2.me/submissions/47f5a22d-904e-44e6-adba-f53e59154508

module
public import Definitions.Def_PretorsionImageClosed_LinearQuiver_Interval
public import Definitions.Def_PretorsionImageClosed_Subobjects_Preimage
public import Definitions.Def_PretorsionImageClosed_Length_Representations
public import Mathlib.CategoryTheory.Limits.FunctorCategory.EpiMono
public import Definitions.Def_PretorsionImageClosed_LinearQuiver_Hom
public import Theorems.Thm_PretorsionImageClosed_LinearQuiver_unit_val

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
theorem _root_.solution {c d a b : Fin n} (hac : a ≤ c) (hbd : b ≤ d) (i : Fin n) :
    coord (canonicalHom (k := k) hac hbd) i = if c ≤ i ∧ i ≤ b then 1 else 0 := by
  unfold coord
  change ((inclusionOrZero k _ _ (unit k c d i) : intervalSpace k a b i) : k) = _
  rw [coe_inclusionOrZero_intervalSpace hac hbd, unit_val]
  by_cases hi : c ≤ i ∧ i ≤ d
  · by_cases hib : i ≤ b
    · rw [if_pos hib, if_pos hi, if_pos ⟨hi.1, hib⟩]
    · rw [if_neg hib, if_neg (show ¬ (c ≤ i ∧ i ≤ b) from fun h => hib h.2)]
  · rw [if_neg (show ¬ (c ≤ i ∧ i ≤ b) from fun h => hi ⟨h.1, h.2.trans hbd⟩)]
    split_ifs <;> rfl
end PretorsionImageClosed.LinearQuiver
