-- Prove2me | solution 1 for TreeStack.one_vertex_flux_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T22:13:26.873339+00:00
-- url     : https://prove2.me/submissions/250d8c2a-0778-4ea2-8f89-cd98be1c8259

import Mathlib
import Definitions.Def_TreeStack_Basic
import Definitions.Def_TreeStack_Transfer

set_option autoImplicit false
open TreeStack
namespace TreeStack
theorem _root_.solution {y A B : ℤ}
    (hA : 1 ≤ A) (hB : 0 ≤ B) (hbal : y + B - 2 * A = 0) :
    A - 2 * B ≤ F y := by
  unfold F
  split_ifs <;> omega
end TreeStack
