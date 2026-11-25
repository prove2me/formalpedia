-- Prove2me | solution 1 for SZ.exists_mem_MahlerZ_Ioo_two_three
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T03:04:22.620183+00:00
-- url     : https://prove2.me/submissions/acaa2771-1ce6-435c-8392-a6230eea2f9d

import Definitions.Def_SZ_SliceHygiene
import Definitions.Def_SZ_SqrtTwo
import Definitions.Def_SZ_SqrtThree
import Definitions.Def_SZ_Tijdeman
import Mathlib.Tactic.IntervalCases
import Definitions.Def_SZ_Cells
import Theorems.Thm_SZ_sqrtFive_mem_MahlerZ

set_option autoImplicit false
open SZ
namespace SZ
theorem _root_.solution : ∃ α ∈ MahlerZ, 2 < α ∧ α < 3 :=
  ⟨Real.sqrt 5, sqrtFive_mem_MahlerZ, by have := s5_lb; linarith, by have := s5_ub; linarith⟩
end SZ
