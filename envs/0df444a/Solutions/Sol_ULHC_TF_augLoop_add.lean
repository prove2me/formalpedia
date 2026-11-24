-- Prove2me | solution 1 for ULHC.TF.augLoop_add
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T05:41:17.563172+00:00
-- url     : https://prove2.me/submissions/5f2ce983-3e72-4508-bec6-a59a092d4e99

import Definitions.Def_ULHC_StripCount
import Definitions.Def_ULHC_TwoFactor
import Theorems.Thm_ULHC_Edge_hi_mk
import Theorems.Thm_ULHC_Edge_lo_h
import Theorems.Thm_ULHC_Edge_lo_v
import Theorems.Thm_ULHC_Edge_q_h
import Theorems.Thm_ULHC_Edge_q_v
attribute [local simp] ULHC.Edge.hi_mk
attribute [local simp] ULHC.Edge.lo_h
attribute [local simp] ULHC.Edge.lo_v
attribute [local simp] ULHC.Edge.q_h
attribute [local simp] ULHC.Edge.q_v



set_option autoImplicit true
open ULHC
open Finset
open ULHC.TF
namespace ULHC.TF
theorem _root_.solution {V : Finset Pt} :
    ∀ n m F, augStep V (augLoop V n F) = none → augLoop V (n + m) F = augLoop V n F := by
  intro n
  induction n with
  | zero =>
    intro m F h
    cases m with
    | zero => rfl
    | succ m =>
      simp only [augLoop] at h
      simp only [augLoop, h]
  | succ n ih =>
    intro m F h
    rw [Nat.add_right_comm]
    rcases hs : augStep V F with _ | F'
    · simp only [augLoop, hs]
    · simp only [augLoop, hs] at h ⊢
      exact ih m F' h
end ULHC.TF
