-- Prove2me | solution 1 for QEC.Coding.LinearCode.dimension_add_dual_dimension_eq_length
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T17:03:42.032071+00:00
-- url     : https://prove2.me/submissions/190baa1e-58c0-44bc-affa-dcfd129644f7

import Definitions.Def_QEC_Semantics_Core_Definitions
import Definitions.Def_QEC_Coding_Core_Definitions
import Theorems.Thm_QEC_Coding_LinearCode_dimension_le_length
import Theorems.Thm_QEC_Coding_LinearCode_dual_dimension_eq_length_sub_dimension

set_option autoImplicit false
open QEC
open QEC.Coding
universe u v w x
open QEC.Coding.LinearCode
variable {F : Type u} {ι : Type v} [Field F] [Fintype F] [Fintype ι]
namespace QEC.Coding.LinearCode
theorem _root_.solution (C : LinearCode F ι) :
    Dimension C + Dimension C.dual = Length F ι := by
  rw [dual_dimension_eq_length_sub_dimension]
  exact Nat.add_sub_of_le (dimension_le_length C)
end QEC.Coding.LinearCode
