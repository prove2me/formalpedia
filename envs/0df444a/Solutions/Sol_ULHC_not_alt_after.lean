-- Prove2me | solution 1 for ULHC.not_alt_after
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T04:47:12.662776+00:00
-- url     : https://prove2.me/submissions/6f0b9951-ac48-49c0-b509-fd652c98e33c

import Definitions.Def_ULHC_Chain
import Definitions.Def_ULHC_L57
import Theorems.Thm_ULHC_lat1_after
import Theorems.Thm_ULHC_front_after
import Theorems.Thm_ULHC_front_end_after
import Theorems.Thm_ULHC_back_after_j
import Theorems.Thm_ULHC_Edge_hi_mk
import Theorems.Thm_ULHC_Edge_lo_h
import Theorems.Thm_ULHC_Edge_lo_v
import Theorems.Thm_ULHC_Edge_q_h
import Theorems.Thm_ULHC_Edge_q_v
import Theorems.Thm_ULHC_NoTypeIII_at
import Theorems.Thm_ULHC_lat1_eq
attribute [local simp] ULHC.Edge.hi_mk
attribute [local simp] ULHC.Edge.lo_h
attribute [local simp] ULHC.Edge.lo_v
attribute [local simp] ULHC.Edge.q_h
attribute [local simp] ULHC.Edge.q_v



set_option autoImplicit true
open ULHC
open Finset Classical
variable {V : Finset Pt} {F : Finset Edge} {c : Pt} {s : Side} {k : ℕ}
  (hk : k % 2 = 0) (hpat : StripPat F c s (k + 2))
include hk hpat
namespace ULHC
theorem _root_.solution {j : ℕ} (hj : 1 ≤ j) (hj' : j ≤ k + 1) :
    ¬ Alt (flipCol F c s (k + 2)) (cellJ c s j) := by
  intro ha
  have hl1 := lat1_after hk hpat (j := j) (by omega)
  have hb := back_after_j hk hpat hj hj'
  have hf : front (cellJ c s j) s ∈ flipCol F c s (k + 2) ↔ j % 2 = 1 := by
    rcases (show j ≤ k ∨ j = k + 1 by omega) with h | rfl
    · exact front_after hk hpat h
    · constructor
      · intro _; omega
      · intro _; exact front_end_after hk hpat
  rw [lat1_eq] at hl1
  simp only [back, front] at hb hf
  unfold Alt at ha
  generalize hd : cellJ c s j = d at *
  obtain ⟨x, y⟩ := d
  cases s <;> simp only [latA, sideEdge, Side.opp] at hl1 hb hf <;>
    rcases Nat.mod_two_eq_zero_or_one j with h | h <;> simp_all
end ULHC
