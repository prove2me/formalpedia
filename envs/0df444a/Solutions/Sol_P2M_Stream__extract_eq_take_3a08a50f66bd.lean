-- Prove2me | solution 1 for P2M_Stream__extract_eq_take_3a08a50f66bd
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T04:20:56.924047+00:00
-- url     : https://prove2.me/submissions/4a62132b-d454-432b-b922-62e63e677919

import Definitions.Def_AutomataTheory_Mathlib_Imports
import Definitions.Def_AutomataTheory_Sequences_Basic

set_option autoImplicit true
open Function Set Option Stream'
open Stream'
variable {X : Type*}
namespace Stream'
theorem _root_.solution {xs : Stream' X} {n : ℕ} :
    xs.extract 0 n = xs.take n := by
  simp only [extract_eq_drop_take, tsub_zero, drop_zero]
end Stream'
