-- Prove2me | solution 1 for ULHC.ite_or_ne
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T04:53:30.018781+00:00
-- url     : https://prove2.me/submissions/493ec78b-e3ce-4a1f-acca-79d091eb9cd2

import Definitions.Def_ULHC_V2Seq
import Definitions.Def_ULHC_Reroute
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
open Finset Classical
namespace ULHC
theorem _root_.solution {x A B : Pt} (h : A ≠ B) :
    (if x = A ∨ x = B then 1 else 0 : ℕ) = (if x = A then 1 else 0) + (if x = B then 1 else 0) := by
  by_cases h1 : x = A
  · subst h1; simp [h]
  · simp [h1]
end ULHC
