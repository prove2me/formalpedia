-- Prove2me | solution 1 for ULHC.end_arcs
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T04:24:15.964179+00:00
-- url     : https://prove2.me/submissions/32516dca-fa92-46c6-a78d-6fe0bb618a36

import Definitions.Def_ULHC_Phase
import Definitions.Def_ULHC_Phase2
import Theorems.Thm_ULHC_par_cellJ
import Theorems.Thm_ULHC_horiz_opp
import Theorems.Thm_ULHC_horiz_latA
import Theorems.Thm_ULHC_horiz_latB
import Theorems.Thm_ULHC_side_cases
import Theorems.Thm_ULHC_Edge_hi_mk
import Theorems.Thm_ULHC_Edge_lo_h
import Theorems.Thm_ULHC_Edge_lo_v
import Theorems.Thm_ULHC_Edge_q_h
import Theorems.Thm_ULHC_Edge_q_v
import Theorems.Thm_ULHC_NoTypeIII_at
import Theorems.Thm_ULHC_back_cellJ_succ
import Theorems.Thm_ULHC_cellJ_zero
import Theorems.Thm_ULHC_lat1_eq
import Theorems.Thm_ULHC_lat2_eq
import Theorems.Thm_ULHC_outArc_eq
attribute [local simp] ULHC.Edge.hi_mk
attribute [local simp] ULHC.Edge.lo_h
attribute [local simp] ULHC.Edge.lo_v
attribute [local simp] ULHC.Edge.q_h
attribute [local simp] ULHC.Edge.q_v



set_option autoImplicit true
open ULHC
open Finset Classical
variable {F : Finset Edge} {c : Pt} {s : Side} {o : Bool}
namespace ULHC
theorem _root_.solution {n : ℕ} (hp : ParOK c s o) (hpat : StripPat F c s (n + 1)) (s' : Side) :
    outArc F (cellJ c s n) s' = !o := by
  obtain ⟨hb, hl, hf⟩ := hpat
  have mF : front (cellJ c s n) s ∈ F ↔ n % 2 = 0 := by
    have := hf n (by omega); simp only [lt_self_iff_false, iff_false] at this; rw [this]; omega
  have mB : back (cellJ c s n) s ∈ F ↔ n % 2 = 0 := by
    rcases n with _ | n
    · simp only [cellJ_zero]; simp [hb]
    · rw [back_cellJ_succ]
      have := hf n (by omega)
      have q : n + 1 < n + 1 + 1 := by omega
      simp only [q, iff_true] at this
      rw [this]; omega
  have mL1 : lat1 (cellJ c s n) s ∈ F ↔ n % 2 = 1 := (hl n (by omega)).1
  have mL2 : lat2 (cellJ c s n) s ∈ F ↔ n % 2 = 1 := (hl n (by omega)).2
  rw [outArc_eq, par_cellJ, hp]
  rcases side_cases s s' with h | h | h | h <;> rw [h]
  · have : decide (sideEdge (cellJ c s n) s ∈ F) = decide (n % 2 = 0) := by
      simp only [front] at mF; simp [mF]
    rw [this]
    cases hs : s.horiz <;> cases o <;> rcases Nat.mod_two_eq_zero_or_one n with h | h <;>
      simp [h]
  · have : decide (sideEdge (cellJ c s n) s.opp ∈ F) = decide (n % 2 = 0) := by
      simp only [back] at mB; simp [mB]
    rw [this, horiz_opp]
    cases hs : s.horiz <;> cases o <;> rcases Nat.mod_two_eq_zero_or_one n with h | h <;>
      simp [h]
  · have : decide (sideEdge (cellJ c s n) (latA s) ∈ F) = decide (n % 2 = 1) := by
      rw [lat1_eq] at mL1; simp [mL1]
    rw [this, horiz_latA]
    cases hs : s.horiz <;> cases o <;> rcases Nat.mod_two_eq_zero_or_one n with h | h <;>
      simp [h]
  · have : decide (sideEdge (cellJ c s n) (latB s) ∈ F) = decide (n % 2 = 1) := by
      rw [lat2_eq] at mL2; simp [mL2]
    rw [this, horiz_latB]
    cases hs : s.horiz <;> cases o <;> rcases Nat.mod_two_eq_zero_or_one n with h | h <;>
      simp [h]
end ULHC
