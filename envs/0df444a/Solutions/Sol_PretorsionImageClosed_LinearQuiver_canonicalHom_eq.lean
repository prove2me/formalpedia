-- Prove2me | solution 1 for PretorsionImageClosed.LinearQuiver.canonicalHom_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T03:05:34.984036+00:00
-- url     : https://prove2.me/submissions/50ba2324-077b-4c5b-8831-244c803883d0

module
public import Definitions.Def_PretorsionImageClosed_LinearQuiver_Interval
public import Definitions.Def_PretorsionImageClosed_Subobjects_Preimage
public import Definitions.Def_PretorsionImageClosed_Length_Representations
public import Mathlib.CategoryTheory.Limits.FunctorCategory.EpiMono
public import Definitions.Def_PretorsionImageClosed_LinearQuiver_Hom
public import Theorems.Thm_PretorsionImageClosed_LinearQuiver_unit_val
public import Theorems.Thm_PretorsionImageClosed_LinearQuiver_hom_ext_coord
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
theorem _root_.solution {c d a b : Fin n} (hac : a ≤ c) (hbd : b ≤ d) :
    canonicalHom (k := k) hac hbd = intervalProj k c hbd ≫ intervalIncl k b hac := by
  apply hom_ext_coord
  intro i
  rw [coord_canonicalHom]
  unfold coord
  rw [NatTrans.comp_app]
  symm
  change ((inclusionOrZero k (intervalSpace k c b i) (intervalSpace k a b i)
    (inclusionOrZero k (intervalSpace k c d i) (intervalSpace k c b i) (unit k c d i)) :
      intervalSpace k a b i) : k) = _
  rw [coe_inclusionOrZero_left k hac, coe_inclusionOrZero_right k hbd, unit_val]
  by_cases hi : c ≤ i ∧ i ≤ d
  · by_cases hib : i ≤ b
    · rw [if_pos hib, if_pos hi, if_pos ⟨hi.1, hib⟩]
    · rw [if_neg hib, if_neg (show ¬ (c ≤ i ∧ i ≤ b) from fun h => hib h.2)]
  · rw [if_neg (show ¬ (c ≤ i ∧ i ≤ b) from fun h => hi ⟨h.1, h.2.trans hbd⟩)]
    split_ifs <;> rfl
end PretorsionImageClosed.LinearQuiver
