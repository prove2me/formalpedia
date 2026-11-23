-- Prove2me | solution 1 for P2M_Stream__take_one_cce64286f92b
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T04:20:35.675561+00:00
-- url     : https://prove2.me/submissions/cf8a7c56-3079-4ae8-9d17-91d636284810

import Definitions.Def_AutomataTheory_Mathlib_Imports
import Definitions.Def_AutomataTheory_Sequences_Basic

set_option autoImplicit true
open Function Set Option Stream'
open Stream'
variable {X : Type*}
namespace Stream'
theorem _root_.solution {xs : Stream' X} :
    xs.take 1 = [xs.get 0] := by
  simp only [take_succ, take_zero]
end Stream'
