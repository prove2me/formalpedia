-- Prove2me | solution 1 for P2M_Stream__get_append_left__364c5eb8ed49
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T04:13:25.261839+00:00
-- url     : https://prove2.me/submissions/ec85b309-1af2-435f-b803-cd81580a4173

import Definitions.Def_AutomataTheory_Mathlib_Imports
import Definitions.Def_AutomataTheory_Sequences_Basic

set_option autoImplicit true
open Function Set Option Stream'
open Stream'
variable {X : Type*}
namespace Stream'
theorem _root_.solution {xl : List X} {xs : Stream' X} {k : ℕ} (h : k < xl.length) :
    (xl ++ₛ xs) k = xl[k] := by
  apply get_append_left
end Stream'
