-- Prove2me | solution 1 for ULHC.reroute_fwd
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T04:58:29.330831+00:00
-- url     : https://prove2.me/submissions/caa2fba6-511a-4a43-8e47-54462141b84d

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
import Theorems.Thm_ULHC_front_mem_next
import Theorems.Thm_ULHC_ind_le_one
import Theorems.Thm_ULHC_isCell_corners
import Theorems.Thm_ULHC_lat1_after
import Theorems.Thm_ULHC_lat1_mem_self
import Theorems.Thm_ULHC_lat1_not_mem
import Theorems.Thm_ULHC_lat2_after
import Theorems.Thm_ULHC_lat2_mem_self
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
    (hlight : ∀ e ∈ B, e ∉ F) (h0 : ∀ e ∈ B, e ∉ cellE c)
    (hu : ∀ e ∈ B, e ∉ cellE (cellJ c s (k + 1))) :
    ∃ B' : Finset Edge, (∀ x, IsCell V x → sidesIn B' x % 2 = 0) ∧
      (∀ e ∈ B', e ∉ flipCol F c s (k + 2)) ∧
      (∀ e ∈ B', e ∉ cellE c ∧ e ∉ cellE (cellJ c s (k + 1))) ∧
      (∀ e, (∀ j, e ∉ Tsw c s j) → (e ∈ B' ↔ e ∈ B)) := by
  set F' := flipCol F c s (k + 2)
  -- Odd cells' lateral sides and fronts are dark in `F`.
  have latO : ∀ j ≤ k + 1, j % 2 = 1 → lat1 (cellJ c s j) s ∉ B ∧ lat2 (cellJ c s j) s ∉ B :=
    fun j hj ho => ⟨fun h => hlight _ h ((hpat.2.1 j (by omega)).1.2 ho),
      fun h => hlight _ h ((hpat.2.1 j (by omega)).2.2 ho)⟩
  have frO : ∀ j ≤ k, j % 2 = 1 → front (cellJ c s j) s ∉ B := by
    intro j hj ho h
    have q : j + 1 < k + 2 := by omega
    exact hlight _ h ((hpat.2.2 j (by omega)).2 (by simp [q]; exact ho))
  -- Fronts of even cells are not in `B` (parity at the next, odd, cell).
  have frE : ∀ j ≤ k, j % 2 = 0 → front (cellJ c s j) s ∉ B := by
    intro j hj he hfB
    rcases (show j + 1 ≤ k ∨ j = k by omega) with hjk | rfl
    · have hev := heven _ (hcell (j + 1) (by omega))
      rw [sidesIn_frame B _ s, back_cellJ_succ] at hev
      have i1 : ind B (front (cellJ c s (j + 1)) s) = 0 := by
        simp [ind, frO (j + 1) hjk (by omega)]
      have i2 : ind B (lat1 (cellJ c s (j + 1)) s) = 0 := by
        simp [ind, (latO (j + 1) (by omega) (by omega)).1]
      have i3 : ind B (lat2 (cellJ c s (j + 1)) s) = 0 := by
        simp [ind, (latO (j + 1) (by omega) (by omega)).2]
      have i4 : ind B (front (cellJ c s j) s) = 1 := by simp [ind, hfB]
      omega
    · exact hu _ hfB (front_mem_next c s j)
  -- At an even interior cell, both lateral sides or neither.
  have pair : ∀ j ≤ k, j % 2 = 0 → 1 ≤ j →
      (lat1 (cellJ c s j) s ∈ B ↔ lat2 (cellJ c s j) s ∈ B) := by
    intro j hj he h1
    obtain ⟨m, rfl⟩ : ∃ m, j = m + 1 := ⟨j - 1, by omega⟩
    have hev := heven _ (hcell (m + 1) (by omega))
    rw [sidesIn_frame B _ s, back_cellJ_succ] at hev
    have i1 : ind B (front (cellJ c s m) s) = 0 := by simp [ind, frO m (by omega) (by omega)]
    have i2 : ind B (front (cellJ c s (m + 1)) s) = 0 := by
      simp [ind, frE (m + 1) hj he]
    rw [i1, i2] at hev
    by_cases h1 : lat1 (cellJ c s (m + 1)) s ∈ B <;> by_cases h2 : lat2 (cellJ c s (m + 1)) s ∈ B <;>
      simp [ind, h1, h2] at hev ⊢
  set J := (Finset.range (k + 1)).filter (fun j => j % 2 = 0 ∧ 1 ≤ j ∧ lat1 (cellJ c s j) s ∈ B)
  have memJ : ∀ j, j ∈ J ↔ j ≤ k ∧ j % 2 = 0 ∧ 1 ≤ j ∧ lat1 (cellJ c s j) s ∈ B := by
    intro j; simp only [J, Finset.mem_filter, Finset.mem_range]
    constructor
    · rintro ⟨a, b, c, d⟩; exact ⟨by omega, b, c, d⟩
    · rintro ⟨a, b, c, d⟩; exact ⟨by omega, b, c, d⟩
  set T := J.biUnion (fun j => Tsw c s (j - 1))
  have hTev : ∀ x, sidesIn T x % 2 = 0 :=
    sidesIn_biUnion_even J (fun j => Tsw c s (j - 1))
      (fun i hi j hj hij => by
        obtain ⟨_, a1, a2, _⟩ := (memJ i).1 hi
        obtain ⟨_, b1, b2, _⟩ := (memJ j).1 hj
        exact Tsw_disj c s (by omega) (by omega) (by omega))
      (fun j _ x => Tsw_even c s (j - 1) x)
  refine ⟨symmDiff B T, ?_, ?_, ?_, ?_⟩
  · intro x hx
    rw [sidesIn_symmDiff]
    have := heven x hx
    have := hTev x
    omega
  · intro e he
    rcases Finset.mem_symmDiff.1 he with ⟨heB, heT⟩ | ⟨heT, heB⟩
    · by_cases hs : ∃ m ≤ k + 1, e ∈ cellE (cellJ c s m)
      · obtain ⟨m, hm, hem⟩ := hs
        rw [cellE_frame _ s] at hem
        simp only [Finset.mem_insert, Finset.mem_singleton] at hem
        rcases hem with rfl | rfl | rfl | rfl
        · rcases m with _ | m
          · exact absurd (by rw [cellJ_zero]; rw [cellE_frame _ s]; simp) (h0 _ heB)
          · rw [back_cellJ_succ] at heB ⊢
            rcases Nat.mod_two_eq_zero_or_one m with he' | ho
            · exact absurd heB (frE m (by omega) he')
            · exact absurd heB (frO m (by omega) ho)
        · rcases (show m ≤ k ∨ m = k + 1 by omega) with hm' | rfl
          · rcases Nat.mod_two_eq_zero_or_one m with he' | ho
            · exact absurd heB (frE m hm' he')
            · exact absurd heB (frO m hm' ho)
          · exact absurd (by rw [cellE_frame _ s]; simp) (hu _ heB)
        · rcases Nat.mod_two_eq_zero_or_one m with he' | ho
          · rcases m with _ | m
            · exact absurd (by have h := lat1_mem_self c s 0; rw [cellJ_zero] at h ⊢; exact h) (h0 _ heB)
            · rcases (show m + 1 ≤ k ∨ m + 1 = k + 1 by omega) with hm' | hm'
              · exact absurd (Finset.mem_biUnion.2 ⟨m + 1, (memJ (m + 1)).2 ⟨hm', he', by omega, heB⟩,
                  by simp [Tsw]⟩) heT
              · omega
          · exact absurd heB (latO m hm ho).1
        · rcases Nat.mod_two_eq_zero_or_one m with he' | ho
          · rcases m with _ | m
            · exact absurd (by have h := lat2_mem_self c s 0; rw [cellJ_zero] at h ⊢; exact h) (h0 _ heB)
            · rcases (show m + 1 ≤ k ∨ m + 1 = k + 1 by omega) with hm' | hm'
              · exact absurd (Finset.mem_biUnion.2 ⟨m + 1,
                  (memJ (m + 1)).2 ⟨hm', he', by omega, (pair (m + 1) hm' he' (by omega)).2 heB⟩,
                  by simp [Tsw]⟩) heT
              · omega
          · exact absurd heB (latO m hm ho).2
      · push Not at hs
        intro hF'
        apply hlight e heB
        have := (mem_after e).1 hF'
        rw [nOn_zero c s (fun m hm => hs m (by omega))] at this
        simpa using this
    · obtain ⟨j, hj, heT'⟩ := Finset.mem_biUnion.1 heT
      obtain ⟨hjk, hje, hj1, hjB⟩ := (memJ j).1 hj
      obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
      simp only [Nat.add_sub_cancel, Tsw, Finset.mem_insert, Finset.mem_singleton] at heT'
      rcases heT' with rfl | rfl | rfl | rfl | rfl | rfl
      · intro h; have := (lat1_after hk hpat (j := i) (by omega)).1 h; omega
      · intro h; have := (lat2_after hk hpat (j := i) (by omega)).1 h; omega
      · exact absurd hjB heB
      · exact absurd ((pair (i + 1) hjk hje hj1).1 hjB) heB
      · -- outer sides of odd cells are light and unchanged
        intro hO
        have hO' := (mem_after _).1 hO
        rw [nOn_zero c s (fun m _ => outer1_not_mem c s i m)] at hO'
        simp only [Nat.zero_mod, iff_true] at hO'
        obtain ⟨_, _, f1V, _⟩ := isCell_corners (hcell i (by omega)) s
        have d1 := deg_front1 (cellJ c s i) s F
        rw [hF.2 _ f1V, nb_cellJ] at d1
        have a1 : ind F (lat1 (cellJ c s i) s) = 1 := by
          simp [ind, (hpat.2.1 i (by omega)).1.2 (by omega)]
        have a2 : ind F (front (cellJ c s i) s) = 1 := by
          have q : i + 1 < k + 2 := by omega
          simp [ind, (hpat.2.2 i (by omega)).2 (by simp [q]; omega)]
        have a3 : ind F (outer1 (cellJ c s i) s) = 1 := by simp [ind, hO']
        have := ind_le_one F (lat1 (cellJ c s (i + 1)) s)
        omega
      · intro hO
        have hO' := (mem_after _).1 hO
        rw [nOn_zero c s (fun m _ => outer2_not_mem c s i m)] at hO'
        simp only [Nat.zero_mod, iff_true] at hO'
        obtain ⟨_, _, _, f2V⟩ := isCell_corners (hcell i (by omega)) s
        have d2 := deg_front2 (cellJ c s i) s F
        rw [hF.2 _ f2V, nb_cellJ] at d2
        have a1 : ind F (lat2 (cellJ c s i) s) = 1 := by
          simp [ind, (hpat.2.1 i (by omega)).2.2 (by omega)]
        have a2 : ind F (front (cellJ c s i) s) = 1 := by
          have q : i + 1 < k + 2 := by omega
          simp [ind, (hpat.2.2 i (by omega)).2 (by simp [q]; omega)]
        have a3 : ind F (outer2 (cellJ c s i) s) = 1 := by simp [ind, hO']
        have := ind_le_one F (lat2 (cellJ c s (i + 1)) s)
        omega
  · intro e he
    rcases Finset.mem_symmDiff.1 he with ⟨heB, _⟩ | ⟨heT, _⟩
    · exact ⟨h0 e heB, hu e heB⟩
    · obtain ⟨j, hj, heT'⟩ := Finset.mem_biUnion.1 heT
      obtain ⟨hjk, hje, hj1, _⟩ := (memJ j).1 hj
      obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
      have z1 := lat1_not_mem c s (j := i) (m := 0) (by omega)
      have z2 := lat2_not_mem c s (j := i) (m := 0) (by omega)
      have z3 := lat1_not_mem c s (j := i + 1) (m := 0) (by omega)
      have z4 := lat2_not_mem c s (j := i + 1) (m := 0) (by omega)
      have z5 := outer1_not_mem c s i 0
      have z6 := outer2_not_mem c s i 0
      rw [cellJ_zero] at z1 z2 z3 z4 z5 z6
      simp only [Nat.add_sub_cancel, Tsw, Finset.mem_insert, Finset.mem_singleton] at heT'
      rcases heT' with rfl | rfl | rfl | rfl | rfl | rfl
      · exact ⟨z1, lat1_not_mem c s (by omega)⟩
      · exact ⟨z2, lat2_not_mem c s (by omega)⟩
      · exact ⟨z3, lat1_not_mem c s (by omega)⟩
      · exact ⟨z4, lat2_not_mem c s (by omega)⟩
      · exact ⟨z5, outer1_not_mem c s i (k + 1)⟩
      · exact ⟨z6, outer2_not_mem c s i (k + 1)⟩
  · intro e he
    have : e ∉ T := fun h => by
      obtain ⟨j, _, hj⟩ := Finset.mem_biUnion.1 h
      exact he (j - 1) hj
    rw [Finset.mem_symmDiff]
    tauto
end ULHC
