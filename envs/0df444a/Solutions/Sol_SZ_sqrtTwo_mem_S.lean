-- Prove2me | solution 1 for SZ.sqrtTwo_mem_S
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T02:41:44.771853+00:00
-- url     : https://prove2.me/submissions/c704bdc7-a3bf-4a8c-b819-531aa8a06ba4

import Definitions.Def_SZ_Defs
import Mathlib.Analysis.Real.Sqrt
import Mathlib.NumberTheory.Real.Irrational
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Definitions.Def_SZ_SqrtTwo
import Theorems.Thm_SZ_one_lt_sqrt_two
import Theorems.Thm_SZ_sqrtTwo_notMem_MahlerZ

set_option autoImplicit false
open SZ
namespace SZ
theorem _root_.solution : Real.sqrt 2 ∈ S := ⟨one_lt_sqrt_two, sqrtTwo_notMem_MahlerZ⟩
end SZ
