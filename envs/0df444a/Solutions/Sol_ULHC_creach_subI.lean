-- Prove2me | solution 1 for ULHC.creach_subI
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T05:23:00.687035+00:00
-- url     : https://prove2.me/submissions/bae403af-adc1-4f29-97d7-96b14f9ff089

import Definitions.Def_ULHC_Algorithm
import Definitions.Def_ULHC_CostConn
import Theorems.Thm_ULHC_fnbr_sub
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
open Finset
namespace ULHC
theorem _root_.solution {V : Finset Pt} {F : Finset Edge} (hFV : Inside V F) (x : Pt) :
    ∀ k, creach F x k ⊆ insert x V := by
  intro k
  induction k with
  | zero => simp [creach]
  | succ k ih =>
    intro z hz
    simp only [creach, mem_union, mem_biUnion] at hz
    rcases hz with hz | ⟨u, _, hz⟩
    · exact ih hz
    · exact mem_insert_of_mem (fnbr_sub hFV u hz)
end ULHC
