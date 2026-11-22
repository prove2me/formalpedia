-- Prove2me | solution 1 for case_one_div_g_not_three
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T08:46:29.612513+00:00
-- url     : https://prove2.me/submissions/572ea1b8-7411-4869-9c7f-31862f1ceb38

import Definitions.Def_Polychromatic_FourThree_Combi_BlockColour
import Definitions.Def_Polychromatic_FourThree_Combi_CaseOne
import Theorems.Thm_HasPolychromColouring_of_image
import Theorems.Thm_hasPolychromColouring_neg
import Theorems.Thm_hasPolychromColouring_univ
import Theorems.Thm_polychromNumber_pair
import Theorems.Thm_polychromNumber_singleton
import Theorems.Thm_polychromNumber_univ
attribute [local simp] hasPolychromColouring_neg
attribute [local simp] hasPolychromColouring_univ
attribute [local simp] polychromNumber_pair
attribute [local simp] polychromNumber_singleton
attribute [local simp] polychromNumber_univ



set_option autoImplicit true
open Finset Pointwise
variable (m : ℕ)
theorem _root_.solution (g : ℕ) (h_div : m = 3 * g ∨ m = 3 * g + 3) (hg3 : g % 3 ≠ 0) :
    HasPolychromColouring (Fin 3) ({0, 1, (g : ZMod m), (g : ZMod m) + 1} : Finset (ZMod m)) := by
  have h3_dvd : 3 ∣ m := by grind
  haveI : NeZero m := ⟨by grind⟩
  apply HasPolychromColouring.of_image (ZMod.castHom h3_dvd (ZMod 3))
  simp only [Finset.image_insert, Finset.image_singleton,
    map_zero, map_one, map_add, map_natCast]
  have hg12 : g % 3 = 1 ∨ g % 3 = 2 := by grind
  suffices ({0, 1, (g : ZMod 3), (g : ZMod 3) + 1} : Finset (ZMod 3)) = Finset.univ by
    rw [this]; exact hasPolychromColouring_univ
  have : (g : ZMod 3) = ↑(g % 3 : ℕ) := by rw [ZMod.natCast_mod]
  rcases hg12 with h | h <;> (simp only [this, h]; decide)
