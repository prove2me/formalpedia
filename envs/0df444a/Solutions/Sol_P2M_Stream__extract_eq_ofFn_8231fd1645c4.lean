-- Prove2me | solution 1 for P2M_Stream__extract_eq_ofFn_8231fd1645c4
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T04:13:59.773247+00:00
-- url     : https://prove2.me/submissions/08c89012-26e1-49b0-9014-8a49fbe79852

import Definitions.Def_AutomataTheory_Mathlib_Imports
import Definitions.Def_AutomataTheory_Sequences_Basic
import Theorems.Thm_P2M_Stream__get_drop__05b839498f63

set_option autoImplicit true
open Function Set Option Stream'
open Stream'
variable {X : Type*}
namespace Stream'
theorem _root_.solution {xs : Stream' X} {m n : ℕ} :
    xs.extract m n = List.ofFn (fun k : Fin (n - m) ↦ xs (m + k)) := by
  ext k x ; rcases (show k < n - m ∨ ¬ k < n - m by omega) with h_k | h_k
    <;> simp (disch := omega) [extract_eq_drop_take, get.eq_1, getElem?_take, get_drop']
    <;> aesop
end Stream'
