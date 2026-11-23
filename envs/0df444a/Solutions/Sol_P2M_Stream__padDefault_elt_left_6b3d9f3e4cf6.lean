-- Prove2me | solution 1 for P2M_Stream__padDefault_elt_left_6b3d9f3e4cf6
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T04:18:16.865999+00:00
-- url     : https://prove2.me/submissions/9561bdb5-00fa-4d55-8156-2b2e44f921c3

import Definitions.Def_AutomataTheory_Mathlib_Imports
import Definitions.Def_AutomataTheory_Sequences_Basic

set_option autoImplicit true
open Function Set Option Stream'
open Stream'
variable {X : Type*}
namespace Stream'
theorem _root_.solution [Inhabited X] {xl : List X} {k : ℕ} (h : k < xl.length) :
    xl.padDefault k = xl[k] := by
  simp [List.padDefault, h]
end Stream'
