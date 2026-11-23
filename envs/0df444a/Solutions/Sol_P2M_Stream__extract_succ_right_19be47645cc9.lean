-- Prove2me | solution 1 for P2M_Stream__extract_succ_right_19be47645cc9
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T04:31:54.1368+00:00
-- url     : https://prove2.me/submissions/d81d5c7e-a36f-4c9f-96bf-9c503bfcc699

import Definitions.Def_AutomataTheory_Mathlib_Imports
import Definitions.Def_AutomataTheory_Sequences_Basic
import Theorems.Thm_P2M_Stream__take_one_cce64286f92b
import Theorems.Thm_P2M_Stream__append_extract_extract_2ca0e177dfc2

set_option autoImplicit true
open Function Set Option Stream'
open Stream'
variable {X : Type*}
namespace Stream'
theorem _root_.solution {xs : Stream' X} {m n : ℕ} (h_mn : m ≤ n) :
    xs.extract m (n + 1) = xs.extract m n ++ [xs.get n] := by
  rw [← append_extract_extract h_mn (show n ≤ n + 1 by omega)] ; congr
  simp only [extract_eq_drop_take, add_tsub_cancel_left, take_one, get_drop, add_zero]
end Stream'
