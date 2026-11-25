-- Prove2me | solution 1 for PretorsionImageClosed.LinearQuiver.card_adm_glue
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T04:41:48.597622+00:00
-- url     : https://prove2.me/submissions/f3ef4958-d28d-4d71-8130-9b3be0ea4f7f

module
public import Definitions.Def_PretorsionImageClosed_LinearQuiver_IntervalFamilies
public import Definitions.Def_PretorsionImageClosed_Gandhi_ColumnSum
public import Definitions.Def_PretorsionImageClosed_LinearQuiver_FamilyRestriction
public import Theorems.Thm_PretorsionImageClosed_LinearQuiver_card_adm
public import Theorems.Thm_PretorsionImageClosed_LinearQuiver_card_admFin_glue

set_option autoImplicit true
@[expose] public section
public section
set_option autoImplicit false
noncomputable section
open PretorsionImageClosed
open Statement Polynomial Finset
open PretorsionImageClosed.LinearQuiver
variable {n : ℕ}
namespace PretorsionImageClosed.LinearQuiver
theorem _root_.solution {D : IntervalFamily n} {J : Finset (Fin (n + 1))} (hJ : J ⊆ adm D) :
    (adm (D.glue J)).card = admCount (adm D) J := by
  rw [card_adm, admCount]
  have := card_admFin_glue hJ
  have e : ((adm D).filter (fun c => ∀ a ∈ J, c ≤ a)).card =
      ((adm D).filter (fun c => ∀ j ∈ J, c ≤ j)).card := by
    congr 1
  split_ifs at this ⊢
  · rw [add_zero] at this
    rw [this, e]
    ring_nf <;> congr
  · rw [this, e]
    ring_nf <;> congr
end PretorsionImageClosed.LinearQuiver
