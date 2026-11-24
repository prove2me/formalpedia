-- Prove2me | solution 1 for ULHC.darkened
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T04:42:43.904942+00:00
-- url     : https://prove2.me/submissions/c94562a1-5b26-4190-a640-2261ef327d90

import Definitions.Def_ULHC_Chain
import Definitions.Def_ULHC_L57
import Theorems.Thm_ULHC_mem_after
import Theorems.Thm_ULHC_Edge_hi_mk
import Theorems.Thm_ULHC_Edge_lo_h
import Theorems.Thm_ULHC_Edge_lo_v
import Theorems.Thm_ULHC_Edge_q_h
import Theorems.Thm_ULHC_Edge_q_v
import Theorems.Thm_ULHC_NoTypeIII_at
import Theorems.Thm_ULHC_back_cellJ_succ
import Theorems.Thm_ULHC_cellE_frame
import Theorems.Thm_ULHC_cellJ_zero
import Theorems.Thm_ULHC_nOn_front_mid
attribute [local simp] ULHC.Edge.hi_mk
attribute [local simp] ULHC.Edge.lo_h
attribute [local simp] ULHC.Edge.lo_v
attribute [local simp] ULHC.Edge.q_h
attribute [local simp] ULHC.Edge.q_v



set_option autoImplicit true
open ULHC
open Finset Classical
variable {V : Finset Pt} {F : Finset Edge} {c : Pt} {s : Side} {k : ℕ}
  (hF : Deg2 V F) (hT : NoTypeIII V F) (hk : k % 2 = 0)
  (hcell : ∀ j ≤ k + 1, IsCell V (cellJ c s j)) (hpat : StripPat F c s (k + 2))
  (hsep : ¬ Conn F (back1 c s) (front1 c s))
include hk hpat
namespace ULHC
theorem _root_.solution {e : Edge} (h1 : e ∈ flipCol F c s (k + 2)) (h2 : e ∉ F) :
    (∃ j ≤ k, j % 2 = 0 ∧ (e = lat1 (cellJ c s j) s ∨ e = lat2 (cellJ c s j) s)) ∨
      e = front (cellJ c s (k + 1)) s := by
  rw [mem_after] at h1
  have hodd : nOn c s (k + 2) e % 2 = 1 := by
    by_contra h; exact h2 (h1.2 (by omega))
  have hne : nOn c s (k + 2) e ≠ 0 := by omega
  unfold nOn at hne
  obtain ⟨m, hm⟩ := Finset.card_ne_zero.1 hne
  simp only [Finset.mem_filter, Finset.mem_range] at hm
  obtain ⟨hmk, hme⟩ := hm
  rw [cellE_frame _ s] at hme
  simp only [Finset.mem_insert, Finset.mem_singleton] at hme
  rcases hme with h | h | h | h
  · -- a back side
    exfalso
    rcases m with _ | m
    · rw [cellJ_zero] at h; rw [h] at h2; exact h2 hpat.1
    · rw [back_cellJ_succ] at h
      rw [h, nOn_front_mid c s (by omega)] at hodd; omega
  · rcases (show m ≤ k ∨ m = k + 1 by omega) with hm' | rfl
    · exfalso; rw [h, nOn_front_mid c s (by omega)] at hodd; omega
    · exact Or.inr h
  · left
    refine ⟨m, ?_, ?_, Or.inl h⟩
    · by_contra hm'
      have : m = k + 1 := by omega
      subst this
      exact h2 (h ▸ (hpat.2.1 (k + 1) (by omega)).1.2 (by omega))
    · by_contra hm'
      exact h2 (h ▸ (hpat.2.1 m hmk).1.2 (by omega))
  · left
    refine ⟨m, ?_, ?_, Or.inr h⟩
    · by_contra hm'
      have : m = k + 1 := by omega
      subst this
      exact h2 (h ▸ (hpat.2.1 (k + 1) (by omega)).2.2 (by omega))
    · by_contra hm'
      exact h2 (h ▸ (hpat.2.1 m hmk).2.2 (by omega))
end ULHC
