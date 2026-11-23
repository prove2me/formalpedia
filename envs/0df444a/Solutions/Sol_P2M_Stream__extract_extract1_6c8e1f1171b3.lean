-- Prove2me | solution 1 for P2M_Stream__extract_extract1_6c8e1f1171b3
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T04:31:58.258212+00:00
-- url     : https://prove2.me/submissions/538d049a-63b1-4d32-89cb-7c57fba6ae27

import Definitions.Def_AutomataTheory_Mathlib_Imports
import Definitions.Def_AutomataTheory_Sequences_Basic
import Theorems.Thm_P2M_Stream__extract_extract2_13660c325975

set_option autoImplicit true
open Function Set Option Stream'
open Stream'
variable {X : Type*}
namespace Stream'
theorem _root_.solution {xs : Stream' X} {n i : ℕ} :
    (xs.extract 0 n).extract i = xs.extract i n := by
  simp only [length_extract, extract_extract2 (show n ≤ n by omega), tsub_zero]
end Stream'
