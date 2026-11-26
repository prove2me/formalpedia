-- Prove2me | solution 1 for Scott1976.DataTypesAsLattices.eq_2_5
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T04:04:28.241066+00:00
-- url     : https://prove2.me/submissions/88d2c2a7-bcde-475a-815f-00f9c9b3bf36

import Definitions.Def_Scott1976_DataTypesAsLattices_Embedding
import Definitions.Def_Scott1976_DataTypesAsLattices_Lambda
import Theorems.Thm_Scott1976_DataTypesAsLattices_mem_ofNat
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
theorem _root_.solution : succSet (ofNat 6 ∪ ofNat 10) = ofNat 7 ∪ ofNat 11 := by
  ext k
  constructor
  · intro ⟨n, hn, hk⟩
    rcases hn with h6 | h10
    · simp [ofNat] at h6; subst h6; simp [ofNat, hk]
    · simp [ofNat] at h10; subst h10; simp [ofNat, hk]
  · intro hk
    rcases hk with h7 | h11
    · simp [ofNat] at h7; exact ⟨6, Or.inl (by simp [ofNat]), by simp [h7]⟩
    · simp [ofNat] at h11; exact ⟨10, Or.inr (by simp [ofNat]), by simp [h11]⟩
end Scott1976.DataTypesAsLattices
