-- Prove2me | solution 1 for case_one_small_g
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T08:49:54.158312+00:00
-- url     : https://prove2.me/submissions/76796d6e-500c-4de8-86e8-2fc9ac146129

import Definitions.Def_Polychromatic_FourThree_Combi_BlockColour
import Definitions.Def_Polychromatic_FourThree_Combi_CaseOne
import Theorems.Thm_table1_0123
import Theorems.Thm_table1_0134
import Theorems.Thm_table1_0145


set_option autoImplicit true
open Finset Pointwise
variable (m : ℕ)
theorem _root_.solution (g : ℕ) (hm : m ≥ 289) (hg : g ∈ ({2, 3, 4} : Finset ℕ)) :
    HasPolychromColouring (Fin 3) ({0, 1, (g : ZMod m), (g : ZMod m) + 1} : Finset (ZMod m)) := by
  fin_cases hg <;> push_cast <;> norm_num
  · exact table1_0123 m (by grind)
  · exact table1_0134 m (by grind)
  · exact table1_0145 m (by grind)
