-- Prove2me | solution 1 for PretorsionImageClosed.LinearQuiver.card_adm
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T04:08:14.081334+00:00
-- url     : https://prove2.me/submissions/b7b320be-e22d-4184-89cd-8199727afe51

module
public import Definitions.Def_PretorsionImageClosed_LinearQuiver_IntervalFamilies
public import Definitions.Def_PretorsionImageClosed_Gandhi_ColumnSum
public import Definitions.Def_PretorsionImageClosed_LinearQuiver_FamilyRestriction

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
theorem _root_.solution (D : IntervalFamily n) : (adm D).card = (admFin D).card + 1 := by
  rw [adm, Finset.card_insert_of_notMem, Finset.card_map]
  simp only [Finset.mem_map, not_exists, not_and]
  intro a _ h
  exact (Fin.castSucc_lt_last a).ne h
end PretorsionImageClosed.LinearQuiver
