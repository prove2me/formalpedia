-- Prove2me | solution 1 for ULHC.mid_touch
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T04:36:40.862999+00:00
-- url     : https://prove2.me/submissions/837354dc-e18b-4ed2-8cb9-1b6016d1f31b

import Definitions.Def_ULHC_Touch
import Definitions.Def_ULHC_Stacked
import Definitions.Def_ULHC_NearGeo
import Theorems.Thm_ULHC_Adj_symm
import Theorems.Thm_ULHC_Conn_symm
import Theorems.Thm_ULHC_Edge_hi_mk
import Theorems.Thm_ULHC_Edge_lo_h
import Theorems.Thm_ULHC_Edge_lo_v
import Theorems.Thm_ULHC_Edge_q_h
import Theorems.Thm_ULHC_Edge_q_v
import Theorems.Thm_ULHC_Ends_inc_iff
import Theorems.Thm_ULHC_Ends_ne_at
import Theorems.Thm_ULHC_Ends_swap
import Theorems.Thm_ULHC_PStep_symm
import Theorems.Thm_ULHC_cellE_frame
import Theorems.Thm_ULHC_corners4
import Theorems.Thm_ULHC_ends_front
import Theorems.Thm_ULHC_ends_lat1
import Theorems.Thm_ULHC_ends_lat2
import Theorems.Thm_ULHC_stk_b1_f2
import Theorems.Thm_ULHC_stk_b2_f1
import Theorems.Thm_ULHC_strip_sig
import Theorems.Thm_ULHC_three_le_deg
attribute [local simp] ULHC.Edge.hi_mk
attribute [local simp] ULHC.Edge.lo_h
attribute [local simp] ULHC.Edge.lo_v
attribute [local simp] ULHC.Edge.q_h
attribute [local simp] ULHC.Edge.q_v



set_option autoImplicit true
open ULHC
open Finset
variable {V : Finset Pt} {F : Finset Edge} {c : Pt} {s : Side} {k : ℕ}
  (hF : Deg2 V F) (hpat : StripPat F c s (k + 2))
  (hcell : ∀ j ≤ k + 1, IsCell V (cellJ c s j))
include hF hpat hcell
namespace ULHC
theorem _root_.solution {p : Pt} (hm : IsMid c s k p) {x : Edge} (hx : x ∈ F) (hxp : x.p = p ∨ x.q = p) :
    ∃ j < k + 2, x ∈ cellE (cellJ c s j) := by
  obtain ⟨j, hj, hjk, hp⟩ := hm
  obtain ⟨a1, a2, _, af⟩ := strip_sig hpat (show j < k + 2 by omega)
  have l1 := a1.2 hj
  have l2 := a2.2 hj
  have fr : front (cellJ c s j) s ∈ F := af.2 ⟨fun _ => by omega, fun _ => hj⟩
  have hdeg := hF.2 _ (corners4 (hcell j (by omega)) s).2.2.1
  have hdeg2 := hF.2 _ (corners4 (hcell j (by omega)) s).2.2.2
  set d := cellJ c s j
  have mem : ∀ y, y = lat1 d s ∨ y = lat2 d s ∨ y = front d s → y ∈ cellE d := by
    intro y hy; rw [cellE_frame d s]; rcases hy with rfl | rfl | rfl <;> simp
  refine ⟨j, by omega, ?_⟩
  rcases hp with rfl | rfl
  · by_contra hn
    have n1 : x ≠ lat1 d s := fun h => hn (mem _ (Or.inl h))
    have n2 : x ≠ front d s := fun h => hn (mem _ (Or.inr (Or.inr h)))
    have n12 : lat1 d s ≠ front d s :=
      (ends_lat1 d s).ne_at (ends_front d s) (stk_b1_f2 d s)
    have := three_le_deg l1 fr hx ((ends_lat1 d s).inc_iff _ |>.2 (Or.inr rfl))
      ((ends_front d s).inc_iff _ |>.2 (Or.inl rfl)) hxp n12 n1.symm n2.symm
    omega
  · by_contra hn
    have n1 : x ≠ lat2 d s := fun h => hn (mem _ (Or.inr (Or.inl h)))
    have n2 : x ≠ front d s := fun h => hn (mem _ (Or.inr (Or.inr h)))
    have n12 : lat2 d s ≠ front d s :=
      (ends_lat2 d s).ne_at (ends_front d s).swap (stk_b2_f1 d s)
    have := three_le_deg l2 fr hx ((ends_lat2 d s).inc_iff _ |>.2 (Or.inr rfl))
      ((ends_front d s).inc_iff _ |>.2 (Or.inr rfl)) hxp n12 n1.symm n2.symm
    omega
end ULHC
