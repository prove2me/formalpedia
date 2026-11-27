-- Prove2me | solution 1 for TreeStack.one_vertex_flux_mod_three
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T22:13:30.3768+00:00
-- url     : https://prove2.me/submissions/e199cb3d-3676-41a3-9fda-7bd4901ffc54

import Mathlib
import Definitions.Def_TreeStack_Basic
import Definitions.Def_TreeStack_Transfer

set_option autoImplicit false
open TreeStack
namespace TreeStack
theorem _root_.solution {y A B : ℤ}
    (hA : 1 ≤ A) (hB : 0 ≤ B) (hbal : y + B - 2 * A = 0) :
    (A - 2 * B) % 3 = F y % 3 := by
  unfold F
  split_ifs <;> omega
end TreeStack
