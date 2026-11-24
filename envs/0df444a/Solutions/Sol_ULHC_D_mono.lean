-- Prove2me | solution 1 for ULHC.D_mono
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:47:39.51268+00:00
-- url     : https://prove2.me/submissions/51f61d7d-111c-410e-843b-dc858c1cd8f0

import Definitions.Def_ULHC_Walk
import Definitions.Def_ULHC_Phase
import Theorems.Thm_ULHC_Deg2_factor
import Theorems.Thm_ULHC_D_step
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
theorem _root_.solution (o : Bool) (c : Pt) (s : Side) (h : outArc F c s = o) :
    if o then D F H c ≤ D F H (nb c s) else D F H (nb c s) ≤ D F H c := by
  have := D_step hF.factor hH.factor c s
  rw [h] at this
  cases o <;> simp only [Bool.false_eq_true, ite_false, ite_true] at this ⊢ <;>
    split_ifs at this <;> omega
end ULHC
