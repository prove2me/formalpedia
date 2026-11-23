-- Prove2me | solution 1 for P2M_Stream__extract_succ_right__dce2e16ca09b
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T04:32:40.6283+00:00
-- url     : https://prove2.me/submissions/0cfbdf03-7fb2-4f00-92f2-0eba84d841fd

import Definitions.Def_AutomataTheory_Mathlib_Imports
import Definitions.Def_AutomataTheory_Sequences_Basic
import Theorems.Thm_P2M_Stream__extract_succ_right_19be47645cc9

set_option autoImplicit true
open Function Set Option Stream'
open Stream'
variable {X : Type*}
namespace Stream'
theorem _root_.solution {xs : Stream' X} {m n : ℕ} (h_mn : m ≤ n) :
    xs.extract m (n + 1) = xs.extract m n ++ [xs n] := by
  apply extract_succ_right ; exact h_mn
end Stream'
