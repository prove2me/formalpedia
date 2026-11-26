-- Prove2me | solution 1 for Scott1976.DataTypesAsLattices.mem_e_lt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T03:59:45.711533+00:00
-- url     : https://prove2.me/submissions/41270c32-c819-41ac-8cb6-92484c0c902b

import Definitions.Def_Scott1976_DataTypesAsLattices_Embedding
import Definitions.Def_Scott1976_DataTypesAsLattices_Lambda
import Theorems.Thm_P2M_Scott1976_DataTypesAsLattices_lt_two_pow__acf4439c4153
import Theorems.Thm_Scott1976_DataTypesAsLattices_mem_e_le
import Theorems.Thm_Scott1976_DataTypesAsLattices_two_pow_le_of_testBit


set_option autoImplicit true
open Scott1976 Scott1976.DataTypesAsLattices
namespace Scott1976.DataTypesAsLattices
theorem _root_.solution {n k : ℕ} (h : k ∈ e n) : k < n := by
  have hle := mem_e_le h
  rcases eq_or_lt_of_le hle with rfl | hlt
  · exact (lt_irrefl k ((lt_two_pow' k).trans_le (two_pow_le_of_testBit h))).elim
  · exact hlt
end Scott1976.DataTypesAsLattices
