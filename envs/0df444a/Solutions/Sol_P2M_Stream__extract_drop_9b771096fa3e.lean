-- Prove2me | solution 1 for P2M_Stream__extract_drop_9b771096fa3e
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T04:11:23.039478+00:00
-- url     : https://prove2.me/submissions/3a15d3d6-911d-4072-b3d3-87af93de5f87

import Definitions.Def_AutomataTheory_Mathlib_Imports
import Definitions.Def_AutomataTheory_Sequences_Basic

set_option autoImplicit true
open Function Set Option Stream'
open Stream'
variable {X : Type*}
namespace Stream'
theorem _root_.solution {xs : Stream' X} {k m n : ℕ} :
    (xs.drop k).extract m n = xs.extract (k + m) (k + n) := by
  have h1 : k + n - (k + m) = n - m := by omega
  simp only [extract_eq_drop_take, drop_drop, h1]
end Stream'
