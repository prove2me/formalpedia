-- Prove2me | solution 1 for case_one_divisible
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T08:50:59.866631+00:00
-- url     : https://prove2.me/submissions/88164d47-990a-4fa5-be85-2ded8d3bc77c

import Definitions.Def_Polychromatic_FourThree_Combi_BlockColour
import Definitions.Def_Polychromatic_FourThree_Combi_CaseOne
import Theorems.Thm_case_one_div_g_not_three
import Theorems.Thm_case_one_div_3g
import Theorems.Thm_case_one_div_3g3

set_option autoImplicit true
open Finset Pointwise
variable (m : ℕ)
theorem _root_.solution (g : ℕ) (hm : m ≥ 289) (h_div : m = 3 * g ∨ m = 3 * g + 3) :
    HasPolychromColouring (Fin 3) ({0, 1, (g : ZMod m), (g : ZMod m) + 1} : Finset (ZMod m)) := by
  by_cases hg3 : g % 3 = 0
  · rcases h_div with h | h
    · exact case_one_div_3g m g h (Nat.dvd_of_mod_eq_zero hg3) (by grind)
    · exact case_one_div_3g3 m g h (Nat.dvd_of_mod_eq_zero hg3) (by grind)
  · exact case_one_div_g_not_three m g h_div hg3
