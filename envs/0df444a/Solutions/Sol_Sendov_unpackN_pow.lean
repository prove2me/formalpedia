-- Prove2me | solution 1 for Sendov.unpackN_pow
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T19:08:00.909956+00:00
-- url     : https://prove2.me/submissions/ef3f9bf5-0f49-4f37-b268-b1f651f5e130

import Mathlib.Data.List.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Definitions.Def_Sendov_FiniteRange_Pack
import Theorems.Thm_Sendov_unpackN_npev
import Theorems.Thm_Sendov_npev_ppowN
import Theorems.Thm_Sendov_mem_le_npev_one

set_option autoImplicit false
open Sendov
namespace Sendov
theorem _root_.solution (b : ℕ) (hb : 0 < b) (p : List ℕ) (k : ℕ)
    (hbound : npev p 1 ^ k < b) :
    unpackN b (ppowN p k).length (npev p b ^ k) = ppowN p k := by
  rw [← npev_ppowN p b k]
  refine unpackN_npev b hb _ fun a ha => ?_
  have h1 : a ≤ npev (ppowN p k) 1 := mem_le_npev_one _ a ha
  rw [npev_ppowN] at h1
  omega
end Sendov
