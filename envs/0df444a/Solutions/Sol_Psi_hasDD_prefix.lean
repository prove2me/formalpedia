-- Prove2me | solution 1 for Psi.hasDD_prefix
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T23:10:34.415801+00:00
-- url     : https://prove2.me/submissions/e5c8cc90-71e2-468b-93cc-69d2b74eacc5

import Definitions.Def_RequestProject_Psi_PhiBasic
import Definitions.Def_RequestProject_Psi_Area
import Theorems.Thm_Psi_hasDD_cons

set_option autoImplicit true
open Psi
namespace Psi
theorem _root_.solution (s t : List Bool) (h : hasDD (s ++ t) = false) : hasDD s = false := by
  induction s with
  | nil => rfl
  | cons a s' ih =>
    rw [List.cons_append, hasDD_cons a (s' ++ t)] at h
    simp only [Bool.or_eq_false_iff] at h
    obtain ⟨hhd, htl⟩ := h
    rw [hasDD_cons a s']
    simp only [Bool.or_eq_false_iff]
    refine ⟨?_, ih htl⟩
    cases s' with
    | nil => simp
    | cons y ys => simpa using hhd
end Psi
