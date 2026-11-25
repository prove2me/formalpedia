-- Prove2me | solution 1 for PretorsionImageClosed.LinearQuiver.indCard_subcategory_family
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T04:22:20.253947+00:00
-- url     : https://prove2.me/submissions/92e3c571-3a4c-4a03-9809-c0ede682b272

module
public import Definitions.Def_PretorsionImageClosed_LinearQuiver_ImageClosed
public import Definitions.Def_PretorsionImageClosed_LinearQuiver_Counting
public import Definitions.Def_PretorsionImageClosed_Gandhi_Delta
public import Definitions.Def_PretorsionImageClosed_LinearQuiver_IntervalFamilies
public import Theorems.Thm_PretorsionImageClosed_LinearQuiver_indCard_eq


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
theorem _root_.solution (D : IntervalFamily n) :
    indCard (D.subcategory (k := k)).prop = D.D.card := by
  rw [indCard_eq]
  apply Nat.subtype_card
  intro p
  constructor
  · intro h
    exact ⟨D.le_of_mem p h, (D.prop_interval_iff (D.le_of_mem p h)).2 h⟩
  · rintro ⟨h1, h2⟩
    exact (D.prop_interval_iff h1).1 h2
end PretorsionImageClosed.LinearQuiver
