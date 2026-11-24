-- Prove2me | solution 1 for ULHC.TF.ends_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T03:45:38.637802+00:00
-- url     : https://prove2.me/submissions/b40aa249-f946-4cc7-9036-19f373ff2c27

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
theorem _root_.solution {e : Edge} {v : Pt} (hv : e.p = v ∨ e.q = v) (z : Pt) :
    (e.p = z ∨ e.q = z) ↔ (z = v ∨ z = other e v) := by
  unfold other
  by_cases h : e.p = v
  · rw [if_pos h]; subst h; constructor <;> rintro (h | h) <;> simp [h]
  · rw [if_neg h]
    have hq : e.q = v := hv.resolve_left h
    subst hq; constructor <;> rintro (h | h) <;> simp [h]
end ULHC.TF
