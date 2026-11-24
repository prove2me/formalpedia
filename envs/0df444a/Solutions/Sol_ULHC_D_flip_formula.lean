-- Prove2me | solution 1 for ULHC.D_flip_formula
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:04:16.680118+00:00
-- url     : https://prove2.me/submissions/8e75382c-5f44-4b5a-a1a1-c4ae04a82fc4

import Definitions.Def_ULHC_Arcs
import Definitions.Def_ULHC_D
import Theorems.Thm_ULHC_wD_supp
import Theorems.Thm_ULHC_wD_flip_off
import Theorems.Thm_ULHC_wD_flip_on
import Theorems.Thm_ULHC_pot_cellE
import Theorems.Thm_ULHC_Edge_hi_mk
import Theorems.Thm_ULHC_Edge_lo_h
import Theorems.Thm_ULHC_Edge_lo_v
import Theorems.Thm_ULHC_Edge_q_h
import Theorems.Thm_ULHC_Edge_q_v
import Theorems.Thm_ULHC_pot_mono_supp
import Theorems.Thm_ULHC_pot_sub
attribute [local simp] ULHC.Edge.hi_mk
attribute [local simp] ULHC.Edge.lo_h
attribute [local simp] ULHC.Edge.lo_v
attribute [local simp] ULHC.Edge.q_h
attribute [local simp] ULHC.Edge.q_v



set_option autoImplicit true
open ULHC
open Finset
namespace ULHC
theorem _root_.solution (F H : Finset Edge) (c x : Pt) :
    D (flip F c) H x - D F H x =
      (if c.2 = x.2 ∧ c.1 ≤ x.1 then - (if up F (lft c) then 2 else -2) else 0) +
      (if c.2 = x.2 ∧ c.1 < x.1 then - (if up F (rgt c) then 2 else -2) else 0) := by
  let E := symmDiff F H ∪ symmDiff (flip F c) H ∪ cellE c
  have s1 : symmDiff (flip F c) H ⊆ E := by
    intro e he; simp only [E, Finset.mem_union]; tauto
  have s2 : symmDiff F H ⊆ E := by
    intro e he; simp only [E, Finset.mem_union]; tauto
  have s3 : cellE c ⊆ E := by
    intro e he; simp only [E, Finset.mem_union]; tauto
  unfold D
  rw [pot_mono_supp s1 (wD_supp _ _), pot_mono_supp s2 (wD_supp _ _), ← pot_sub]
  have hsupp : Supp (cellE c) (fun e => wD (flip F c) H e - wD F H e) := by
    intro e he; simp [wD_flip_off he]
  rw [← pot_mono_supp s3 hsupp, pot_cellE]
  have hl : lft c ∈ cellE c := by simp [cellE]
  have hr : rgt c ∈ cellE c := by simp [cellE]
  rw [wD_flip_on hl, wD_flip_on hr]
end ULHC
