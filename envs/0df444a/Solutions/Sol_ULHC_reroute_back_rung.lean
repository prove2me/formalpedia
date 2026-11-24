-- Prove2me | solution 1 for ULHC.reroute_back_rung
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T04:58:59.861866+00:00
-- url     : https://prove2.me/submissions/1d888579-f2b6-439c-8b9b-599871211371

import Definitions.Def_ULHC_V2Seq
import Definitions.Def_ULHC_Reroute
import Theorems.Thm_ULHC_Tsw_even
import Theorems.Thm_ULHC_Tsw_disj
import Theorems.Thm_ULHC_sidesIn_biUnion_even
import Theorems.Thm_ULHC_sidesIn_frame
import Theorems.Thm_ULHC_Edge_hi_mk
import Theorems.Thm_ULHC_Edge_lo_h
import Theorems.Thm_ULHC_Edge_lo_v
import Theorems.Thm_ULHC_Edge_q_h
import Theorems.Thm_ULHC_Edge_q_v
import Theorems.Thm_ULHC_NoTypeIII_at
import Theorems.Thm_ULHC_back_cellJ_succ
import Theorems.Thm_ULHC_cellE_frame
import Theorems.Thm_ULHC_cellJ_zero
import Theorems.Thm_ULHC_deg_front1
import Theorems.Thm_ULHC_deg_front2
import Theorems.Thm_ULHC_front_after
import Theorems.Thm_ULHC_front_mem_self
import Theorems.Thm_ULHC_ind_le_one
import Theorems.Thm_ULHC_isCell_corners
import Theorems.Thm_ULHC_lat1_after
import Theorems.Thm_ULHC_lat1_not_mem
import Theorems.Thm_ULHC_lat2_after
import Theorems.Thm_ULHC_lat2_not_mem
import Theorems.Thm_ULHC_mem_after
import Theorems.Thm_ULHC_nOn_zero
import Theorems.Thm_ULHC_nb_cellJ
import Theorems.Thm_ULHC_outer1_not_mem
import Theorems.Thm_ULHC_outer2_not_mem
import Theorems.Thm_ULHC_sidesIn_symmDiff
attribute [local simp] ULHC.Edge.hi_mk
attribute [local simp] ULHC.Edge.lo_h
attribute [local simp] ULHC.Edge.lo_v
attribute [local simp] ULHC.Edge.q_h
attribute [local simp] ULHC.Edge.q_v



set_option autoImplicit true
open ULHC
open Finset Classical
variable {V : Finset Pt} {F : Finset Edge} {c : Pt} {s : Side} {k : ℕ}
  (hF : Deg2 V F) (hk : k % 2 = 0) (hcell : ∀ j ≤ k + 1, IsCell V (cellJ c s j))
  (hpat : StripPat F c s (k + 2))
include hF hk hcell hpat
namespace ULHC
theorem _root_.solution {B : Finset Edge} (heven : ∀ x, IsCell V x → sidesIn B x % 2 = 0)
    (hlight : ∀ e ∈ B, e ∉ flipCol F c s (k + 2)) (h0 : ∀ e ∈ B, e ∉ cellE c)
    (hu : ∀ e ∈ B, e ∈ cellE (cellJ c s (k + 1)) →
      e = lat1 (cellJ c s (k + 1)) s ∨ e = lat2 (cellJ c s (k + 1)) s) :
    ∃ B' : Finset Edge, (∀ x, IsCell V x → sidesIn B' x % 2 = 0) ∧
      (∀ e ∈ B', e ∉ F ∨ e = lat1 (cellJ c s (k + 1)) s ∨ e = lat2 (cellJ c s (k + 1)) s) ∧
      (∀ e ∈ B', e ∉ cellE c ∧ (e ∈ cellE (cellJ c s (k + 1)) →
        e = lat1 (cellJ c s (k + 1)) s ∨ e = lat2 (cellJ c s (k + 1)) s)) ∧
      (∀ e, (∀ j, e ∉ Tsw c s j) → (e ∈ B' ↔ e ∈ B)) := by
  set F' := flipCol F c s (k + 2)
  have hfu : ∀ e ∈ B, e ≠ front (cellJ c s (k + 1)) s := by
    intro e he h
    subst h
    have hf : front (cellJ c s (k + 1)) s ∈ cellE (cellJ c s (k + 1)) := by rw [cellE_frame _ s]; simp
    have nb1 : front (cellJ c s (k + 1)) s ≠ lat1 (cellJ c s (k + 1)) s ∧
        front (cellJ c s (k + 1)) s ≠ lat2 (cellJ c s (k + 1)) s := by
      generalize cellJ c s (k + 1) = r; obtain ⟨x, y⟩ := r
      cases s <;> simp [front, lat1, lat2, sideEdge, bot, top, lft, rgt]
    rcases hu _ he hf with h | h
    · exact nb1.1 h
    · exact nb1.2 h
  -- Even cells' lateral sides and interior fronts are dark in `F'`; fronts are unchanged.
  have latE : ∀ j ≤ k + 1, j % 2 = 0 → lat1 (cellJ c s j) s ∉ B ∧ lat2 (cellJ c s j) s ∉ B :=
    fun j hj he => ⟨fun h => hlight _ h ((lat1_after hk hpat hj).2 he),
      fun h => hlight _ h ((lat2_after hk hpat hj).2 he)⟩
  have frO : ∀ j ≤ k, j % 2 = 1 → front (cellJ c s j) s ∉ B :=
    fun j hj ho h => hlight _ h ((front_after hk hpat hj).2 ho)
  -- Interior fronts of even cells are not in `B` (parity at the even cell).
  have frE : ∀ j ≤ k, j % 2 = 0 → front (cellJ c s j) s ∉ B := by
    intro j hj he hfB
    rcases j with _ | j
    · exact h0 _ hfB (by have h := front_mem_self c s 0; rw [cellJ_zero] at h ⊢; exact h)
    · have hev := heven _ (hcell (j + 1) (by omega))
      rw [sidesIn_frame B _ s, back_cellJ_succ] at hev
      have i1 : ind B (front (cellJ c s j) s) = 0 := by
        simp [ind, frO j (by omega) (by omega)]
      have i2 : ind B (lat1 (cellJ c s (j + 1)) s) = 0 := by
        simp [ind, (latE (j + 1) (by omega) he).1]
      have i3 : ind B (lat2 (cellJ c s (j + 1)) s) = 0 := by
        simp [ind, (latE (j + 1) (by omega) he).2]
      have i4 : ind B (front (cellJ c s (j + 1)) s) = 1 := by simp [ind, hfB]
      omega
  -- At an odd cell, both lateral sides or neither.
  have pair : ∀ j ≤ k, j % 2 = 1 →
      (lat1 (cellJ c s j) s ∈ B ↔ lat2 (cellJ c s j) s ∈ B) := by
    intro j hj ho
    obtain ⟨m, rfl⟩ : ∃ m, j = m + 1 := ⟨j - 1, by omega⟩
    have hev := heven _ (hcell (m + 1) (by omega))
    rw [sidesIn_frame B _ s, back_cellJ_succ] at hev
    have i1 : ind B (front (cellJ c s m) s) = 0 := by simp [ind, frE m (by omega) (by omega)]
    have i2 : ind B (front (cellJ c s (m + 1)) s) = 0 := by simp [ind, frO (m + 1) hj ho]
    rw [i1, i2] at hev
    by_cases h1 : lat1 (cellJ c s (m + 1)) s ∈ B <;> by_cases h2 : lat2 (cellJ c s (m + 1)) s ∈ B <;>
      simp [ind, h1, h2] at hev ⊢
  set J := (Finset.range (k + 1)).filter (fun j => j % 2 = 1 ∧ lat1 (cellJ c s j) s ∈ B)
  set T := J.biUnion (Tsw c s)
  have memJ : ∀ j, j ∈ J ↔ j ≤ k ∧ j % 2 = 1 ∧ lat1 (cellJ c s j) s ∈ B := by
    intro j; simp only [J, Finset.mem_filter, Finset.mem_range]
    constructor
    · rintro ⟨a, b, c⟩; exact ⟨by omega, b, c⟩
    · rintro ⟨a, b, c⟩; exact ⟨by omega, b, c⟩
  have hTev : ∀ x, sidesIn T x % 2 = 0 :=
    sidesIn_biUnion_even J (Tsw c s)
      (fun i hi j hj hij => Tsw_disj c s ((memJ i).1 hi).2.1 ((memJ j).1 hj).2.1 hij)
      (fun j _ x => Tsw_even c s j x)
  refine ⟨symmDiff B T, ?_, ?_, ?_, ?_⟩
  · intro x hx
    rw [sidesIn_symmDiff]
    have := heven x hx
    have := hTev x
    omega
  · intro e he
    by_cases hl : e = lat1 (cellJ c s (k + 1)) s ∨ e = lat2 (cellJ c s (k + 1)) s
    · exact Or.inr hl
    left
    rcases Finset.mem_symmDiff.1 he with ⟨heB, heT⟩ | ⟨heT, heB⟩
    · -- In `B` and not swapped: an unchanged side.
      by_cases hs : ∃ m ≤ k + 1, e ∈ cellE (cellJ c s m)
      · obtain ⟨m, hm, hem⟩ := hs
        rw [cellE_frame _ s] at hem
        simp only [Finset.mem_insert, Finset.mem_singleton] at hem
        rcases hem with rfl | rfl | rfl | rfl
        · -- a back side: the front of the cell before
          rcases m with _ | m
          · exact absurd (by rw [cellJ_zero]; rw [cellE_frame _ s]; simp) (h0 _ heB)
          · rw [back_cellJ_succ] at heB ⊢
            intro hF'
            have hm' : m ≤ k := by omega
            have e1 := (front_after hk hpat hm')
            have e2 := hpat.2.2 m (by omega)
            have q : m + 1 < k + 2 := by omega
            simp only [q, iff_true] at e2
            exact hlight _ heB (e1.2 (e2.1 hF'))
        · rcases (show m ≤ k ∨ m = k + 1 by omega) with hm' | rfl
          · intro hF'
            have e1 := (front_after hk hpat hm')
            have e2 := hpat.2.2 m (by omega)
            have q : m + 1 < k + 2 := by omega
            simp only [q, iff_true] at e2
            exact hlight _ heB (e1.2 (e2.1 hF'))
          · exact absurd rfl (hfu _ heB)
        · rcases Nat.mod_two_eq_zero_or_one m with he' | ho
          · exact absurd heB (latE m hm he').1
          · rcases (show m ≤ k ∨ m = k + 1 by omega) with hm' | rfl
            · exact absurd (Finset.mem_biUnion.2 ⟨m, (memJ m).2 ⟨hm', ho, heB⟩, by simp [Tsw]⟩) heT
            · exact absurd (Or.inl rfl) hl
        · rcases Nat.mod_two_eq_zero_or_one m with he' | ho
          · exact absurd heB (latE m hm he').2
          · rcases (show m ≤ k ∨ m = k + 1 by omega) with hm' | rfl
            · exact absurd (Finset.mem_biUnion.2 ⟨m, (memJ m).2 ⟨hm', ho, (pair m hm' ho).2 heB⟩,
                by simp [Tsw]⟩) heT
            · exact absurd (Or.inr rfl) hl
      · push Not at hs
        intro hF'
        apply hlight e heB
        rw [mem_after, nOn_zero c s (fun m hm => hs m (by omega))]
        simp [hF']
    · -- Swapped in: a lateral side of an even cell, or an outer side.
      obtain ⟨j, hj, heT'⟩ := Finset.mem_biUnion.1 heT
      obtain ⟨hjk, hjo, hjB⟩ := (memJ j).1 hj
      have hjk' : j + 1 ≤ k := by omega
      simp only [Tsw, Finset.mem_insert, Finset.mem_singleton] at heT'
      rcases heT' with rfl | rfl | rfl | rfl | rfl | rfl
      · exact absurd hjB heB
      · exact absurd ((pair j hjk hjo).1 hjB) heB
      · intro h; have := (hpat.2.1 (j + 1) (by omega)).1.1 h; omega
      · intro h; have := (hpat.2.1 (j + 1) (by omega)).2.1 h; omega
      · -- degree count at `front1 c_j`
        intro hO
        obtain ⟨_, _, f1V, _⟩ := isCell_corners (hcell j (by omega)) s
        have d1 := deg_front1 (cellJ c s j) s F
        rw [hF.2 _ f1V, nb_cellJ] at d1
        have a1 : ind F (lat1 (cellJ c s j) s) = 1 := by
          simp [ind, (hpat.2.1 j (by omega)).1.2 hjo]
        have a2 : ind F (front (cellJ c s j) s) = 1 := by
          have q : j + 1 < k + 2 := by omega
          simp [ind, (hpat.2.2 j (by omega)).2 (by simp [q]; exact hjo)]
        have a3 : ind F (outer1 (cellJ c s j) s) = 1 := by simp [ind, hO]
        have := ind_le_one F (lat1 (cellJ c s (j + 1)) s)
        omega
      · intro hO
        obtain ⟨_, _, _, f2V⟩ := isCell_corners (hcell j (by omega)) s
        have d2 := deg_front2 (cellJ c s j) s F
        rw [hF.2 _ f2V, nb_cellJ] at d2
        have a1 : ind F (lat2 (cellJ c s j) s) = 1 := by
          simp [ind, (hpat.2.1 j (by omega)).2.2 hjo]
        have a2 : ind F (front (cellJ c s j) s) = 1 := by
          have q : j + 1 < k + 2 := by omega
          simp [ind, (hpat.2.2 j (by omega)).2 (by simp [q]; exact hjo)]
        have a3 : ind F (outer2 (cellJ c s j) s) = 1 := by simp [ind, hO]
        have := ind_le_one F (lat2 (cellJ c s (j + 1)) s)
        omega
  · intro e he
    rcases Finset.mem_symmDiff.1 he with ⟨heB, _⟩ | ⟨heT, _⟩
    · exact ⟨h0 e heB, hu e heB⟩
    · obtain ⟨j, hj, heT'⟩ := Finset.mem_biUnion.1 heT
      obtain ⟨hjk, hjo, _⟩ := (memJ j).1 hj
      have z1 := lat1_not_mem c s (j := j) (m := 0) (by omega)
      have z2 := lat2_not_mem c s (j := j) (m := 0) (by omega)
      have z3 := lat1_not_mem c s (j := j + 1) (m := 0) (by omega)
      have z4 := lat2_not_mem c s (j := j + 1) (m := 0) (by omega)
      have z5 := outer1_not_mem c s j 0
      have z6 := outer2_not_mem c s j 0
      rw [cellJ_zero] at z1 z2 z3 z4 z5 z6
      simp only [Tsw, Finset.mem_insert, Finset.mem_singleton] at heT'
      rcases heT' with rfl | rfl | rfl | rfl | rfl | rfl
      · exact ⟨z1, fun h => absurd h (lat1_not_mem c s (by omega))⟩
      · exact ⟨z2, fun h => absurd h (lat2_not_mem c s (by omega))⟩
      · exact ⟨z3, fun h => absurd h (lat1_not_mem c s (by omega))⟩
      · exact ⟨z4, fun h => absurd h (lat2_not_mem c s (by omega))⟩
      · exact ⟨z5, fun h => absurd h (outer1_not_mem c s j (k + 1))⟩
      · exact ⟨z6, fun h => absurd h (outer2_not_mem c s j (k + 1))⟩
  · intro e he
    have : e ∉ T := fun h => by
      obtain ⟨j, _, hj⟩ := Finset.mem_biUnion.1 h
      exact he j hj
    rw [Finset.mem_symmDiff]
    tauto
end ULHC
