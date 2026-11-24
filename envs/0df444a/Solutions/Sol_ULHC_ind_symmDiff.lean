-- Prove2me | solution 1 for ULHC.ind_symmDiff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T04:42:51.155111+00:00
-- url     : https://prove2.me/submissions/392aaf62-25ae-42c4-93c8-a186852326df

import Definitions.Def_ULHC_L57
import Definitions.Def_ULHC_Dual
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
theorem _root_.solution (A B : Finset Edge) (e : Edge) :
    ind (symmDiff A B) e % 2 = (ind A e + ind B e) % 2 := by
  simp only [ind, Finset.mem_symmDiff]
  by_cases ha : e ∈ A <;> by_cases hb : e ∈ B <;> simp [ha, hb]
end ULHC
