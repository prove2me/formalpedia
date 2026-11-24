-- Prove2me | solution 1 for ULHC.Good.step
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:49:20.537805+00:00
-- url     : https://prove2.me/submissions/cee79403-cc0b-4b28-bc42-d62970b76c93

import Definitions.Def_ULHC_Walk
import Definitions.Def_ULHC_Phase
import Theorems.Thm_ULHC_D_mono
import Theorems.Thm_ULHC_Edge_hi_mk
import Theorems.Thm_ULHC_Edge_lo_h
import Theorems.Thm_ULHC_Edge_lo_v
import Theorems.Thm_ULHC_Edge_q_h
import Theorems.Thm_ULHC_Edge_q_v
import Theorems.Thm_ULHC_NoTypeIII_at
attribute [local simp] ULHC.Edge.hi_mk
attribute [local simp] ULHC.Edge.lo_h
attribute [local simp] ULHC.Edge.lo_v
attribute [local simp] ULHC.Edge.q_h
attribute [local simp] ULHC.Edge.q_v



set_option autoImplicit true
open ULHC
open Finset Classical
variable {V : Finset Pt} {F H : Finset Edge} (hF : Deg2 V F) (hH : Deg2 V H)
include hF hH
namespace ULHC
namespace Good
theorem _root_.solution {o : Bool} {c : Pt} {s : Side} (h : outArc F c s = o) (hg : Good o (D F H c)) :
    Good o (D F H (nb c s)) := by
  have := D_mono hF hH o c s h
  unfold Good at *
  cases o <;> simp only [Bool.false_eq_true, ite_false, ite_true] at this hg ⊢ <;> omega
end Good
end ULHC
