-- Prove2me | solution 1 for P2M_Stream__extract_extract2_13660c325975
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T04:21:14.841543+00:00
-- url     : https://prove2.me/submissions/5b4f3446-0027-4fed-9c6a-54bc2f8479f6

import Definitions.Def_AutomataTheory_Mathlib_Imports
import Definitions.Def_AutomataTheory_Sequences_Basic
import Theorems.Thm_P2M_Stream__extract_extract2__d35761143a43

set_option autoImplicit true
open Function Set Option Stream'
open Stream'
variable {X : Type*}
namespace Stream'
theorem _root_.solution {xs : Stream' X} {n i j : ℕ} (h : j ≤ n) :
    (xs.extract 0 n).extract i j = xs.extract i j := by
  simp only [extract_extract2' (show j ≤ n - 0 by omega), zero_add]
end Stream'
