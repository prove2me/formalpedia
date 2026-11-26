-- Prove2me | solution 1 for Scott1976.DataTypesAsLattices.seq2_tag_ne
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T04:02:45.40715+00:00
-- url     : https://prove2.me/submissions/867741ab-719f-4c84-92fe-8e7be776d5b8

import Definitions.Def_Scott1976_DataTypesAsLattices_Embedding
import Definitions.Def_Scott1976_DataTypesAsLattices_Lambda
import Theorems.Thm_Scott1976_DataTypesAsLattices_mem_ofNat
import Theorems.Thm_Scott1976_DataTypesAsLattices_seq2_app_zero
import Theorems.Thm_Scott1976_DataTypesAsLattices_mem_botElem
import Theorems.Thm_Scott1976_DataTypesAsLattices_mem_e
import Theorems.Thm_Scott1976_DataTypesAsLattices_mem_topElem
attribute [local simp] Scott1976.DataTypesAsLattices.mem_botElem
attribute [local simp] Scott1976.DataTypesAsLattices.mem_e
attribute [local simp] Scott1976.DataTypesAsLattices.mem_topElem


attribute [local simp] Scott1976.DataTypesAsLattices.mem_ofNat

set_option autoImplicit true
open Scott1976 Scott1976.DataTypesAsLattices
namespace Scott1976.DataTypesAsLattices
theorem _root_.solution (x y : Pomega) :
    seq2 (ofNat 0) x ≠ seq2 (ofNat 1) y := by
  intro h
  have := congrArg (fun w => funOf w (ofNat 0)) h
  simp [seq2_app_zero] at this
  have h0 : (0 : ℕ) ∈ ofNat 1 := by
    rw [← this]; simp [ofNat]
  simp [ofNat] at h0
end Scott1976.DataTypesAsLattices
