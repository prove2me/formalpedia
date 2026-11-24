-- Prove2me | solution 1 for ULHC.sidesIn_biUnion_even
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T04:56:00.77049+00:00
-- url     : https://prove2.me/submissions/98b80c99-12cf-451d-9454-a92571b25a54

import Definitions.Def_ULHC_V2Seq
import Definitions.Def_ULHC_Reroute
import Theorems.Thm_ULHC_ind_union_disj
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
namespace ULHC
theorem _root_.solution (J : Finset ℕ) (f : ℕ → Finset Edge)
    (hd : ∀ i ∈ J, ∀ j ∈ J, i ≠ j → Disjoint (f i) (f j))
    (he : ∀ j ∈ J, ∀ x, sidesIn (f j) x % 2 = 0) (x : Pt) :
    sidesIn (J.biUnion f) x % 2 = 0 := by
  induction J using Finset.induction_on with
  | empty => simp [sidesIn, ind]
  | insert a J ha ih =>
    rw [Finset.biUnion_insert]
    have hdis : Disjoint (f a) (J.biUnion f) := by
      rw [Finset.disjoint_biUnion_right]
      intro j hj
      exact hd a (Finset.mem_insert_self a J) j (Finset.mem_insert_of_mem hj)
        (fun h => ha (h ▸ hj))
    have ih' := ih (fun i hi j hj => hd i (Finset.mem_insert_of_mem hi) j (Finset.mem_insert_of_mem hj))
      (fun j hj => he j (Finset.mem_insert_of_mem hj))
    have h0 := he a (Finset.mem_insert_self a J) x
    unfold sidesIn at *
    rw [ind_union_disj hdis, ind_union_disj hdis, ind_union_disj hdis, ind_union_disj hdis]
    omega
end ULHC
