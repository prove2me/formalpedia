-- Prove2me | solution 1 for QEC.Coding.why24FrobeniusRootFour_pow_four
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T11:20:20.804337+00:00
-- url     : https://prove2.me/submissions/fa9db13a-d45d-42a6-85de-95b800504dda

import Definitions.Def_QEC_Coding_QuditQubitConversion_Transport
import Definitions.Def_QEC_Coding_QuditQubitConversion_U7Gate
import Theorems.Thm_QEC_Coding_f1024_card

section
noncomputable section
namespace QEC.Coding
open scoped BigOperators
private theorem why24_f1024_pow_card (x : F1024) : x ^ 1024 = x := by
  rw [← f1024_card]
  exact FiniteField.pow_card x
end QEC.Coding
end
end

set_option autoImplicit false
noncomputable section
open QEC QEC.Coding
open scoped BigOperators
namespace QEC.Coding
theorem _root_.solution (x : F1024) :
    why24FrobeniusRootFour x ^ 4 = x := by
  change (x ^ 256) ^ 4 = x
  rw [← pow_mul]
  norm_num
  exact why24_f1024_pow_card x
end QEC.Coding
