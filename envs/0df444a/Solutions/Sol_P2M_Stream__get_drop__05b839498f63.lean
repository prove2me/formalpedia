-- Prove2me | solution 1 for P2M_Stream__get_drop__05b839498f63
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T04:11:16.895272+00:00
-- url     : https://prove2.me/submissions/103d59be-d5e4-46e7-9e12-6001369e56d1

import Definitions.Def_AutomataTheory_Mathlib_Imports
import Definitions.Def_AutomataTheory_Sequences_Basic

set_option autoImplicit true
open Function Set Option Stream'
open Stream'
variable {X : Type*}
namespace Stream'
theorem _root_.solution {xs : Stream' X} {n k : ℕ} :
    (xs.drop n) k = xs (n + k) := by
  apply get_drop
end Stream'
