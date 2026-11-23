-- Prove2me | solution 1 for P2M_Stream__take_one__38ffcc18b2b5
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T04:47:27.465069+00:00
-- url     : https://prove2.me/submissions/4e413d3e-7a39-4853-a7b4-e357b960e8a2

import Definitions.Def_AutomataTheory_Mathlib_Imports
import Definitions.Def_AutomataTheory_Sequences_Basic
import Theorems.Thm_P2M_Stream__take_one_cce64286f92b

set_option autoImplicit true
open Function Set Option Stream'
open Stream'
variable {X : Type*}
namespace Stream'
theorem _root_.solution {xs : Stream' X} :
    xs.take 1 = [xs 0] := by
  apply take_one
end Stream'
