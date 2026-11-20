-- Prove2me | solution 1 for Sensitivity.BoolFun.exists_degree_witness
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T18:57:21.636279+00:00
-- url     : https://prove2.me/submissions/61b253ba-7db5-4431-b147-b8c7cb7bfd4f

import Definitions.Def_Sensitivity_Defs
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Int.Basic
import Definitions.Def_Sensitivity_Multilinear
import Theorems.Thm_Sensitivity_indicator_mem
import Theorems.Thm_Sensitivity_indicator_not_mem
import Theorems.Thm_Sensitivity_boolToInt_true
import Theorems.Thm_Sensitivity_boolToInt_false
import Theorems.Thm_Sensitivity_flipBit_apply_ne
import Theorems.Thm_Sensitivity_flipBit_apply_same
import Theorems.Thm_Sensitivity_flipBit_flipBit_same
attribute [local simp] Sensitivity.flipBit_apply_ne
attribute [local simp] Sensitivity.flipBit_apply_same
attribute [local simp] Sensitivity.flipBit_flipBit_same


attribute [local simp] Sensitivity.indicator_mem
attribute [local simp] Sensitivity.indicator_not_mem
attribute [local simp] Sensitivity.boolToInt_true
attribute [local simp] Sensitivity.boolToInt_false

set_option autoImplicit false
open Sensitivity
variable {n : ℕ}
namespace Sensitivity
namespace BoolFun
theorem _root_.solution (f : BoolFun n) (hd : 0 < f.degree) :
    ∃ S : Finset (Fin n), S.card = f.degree ∧ f.moebius S ≠ 0 := by
  unfold degree at hd ⊢
  set F := (Finset.univ : Finset (Finset (Fin n))).filter (fun S => f.moebius S ≠ 0)
  have hne : F.Nonempty := by
    by_contra h
    rw [Finset.not_nonempty_iff_eq_empty] at h
    simp [F, h] at hd
  obtain ⟨S, hS, heq⟩ := Finset.exists_mem_eq_sup F hne Finset.card
  rw [Finset.mem_filter] at hS
  exact ⟨S, heq.symm, hS.2⟩
end BoolFun
end Sensitivity
