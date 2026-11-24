-- Prove2me | solution 1 for ULHC.nOn_rev
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T05:12:58.435794+00:00
-- url     : https://prove2.me/submissions/e39fc68a-3b4c-4a0a-afba-8feea4648968

import Definitions.Def_ULHC_NearLemma
import Definitions.Def_ULHC_Reverse
import Theorems.Thm_ULHC_rev_cellJ
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
theorem _root_.solution (c : Pt) (s : Side) (k : ℕ) (x : Edge) :
    nOn (cellJ c s (k + 1)) s.opp (k + 2) x = nOn c s (k + 2) x := by
  unfold nOn
  apply Finset.card_bij (fun i _ => k + 1 - i)
  · intro i hi
    simp only [Finset.mem_filter, Finset.mem_range] at hi ⊢
    refine ⟨by omega, ?_⟩
    rw [← rev_cellJ c s (by omega)]; exact hi.2
  · intro i hi j hj h
    simp only [Finset.mem_filter, Finset.mem_range] at hi hj
    omega
  · intro j hj
    simp only [Finset.mem_filter, Finset.mem_range] at hj
    refine ⟨k + 1 - j, ?_, by omega⟩
    simp only [Finset.mem_filter, Finset.mem_range]
    refine ⟨by omega, ?_⟩
    rw [rev_cellJ c s (by omega), show k + 1 - (k + 1 - j) = j by omega]; exact hj.2
end ULHC
