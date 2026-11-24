-- Prove2me | solution 1 for ULHC.strip_odd
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T04:24:55.830645+00:00
-- url     : https://prove2.me/submissions/e6a67e17-0862-4467-8111-c52af18f1a5e

import Definitions.Def_ULHC_Strip
import Definitions.Def_ULHC_StripCount
import Theorems.Thm_ULHC_mkBF_cellE
import Theorems.Thm_ULHC_mkLat_cellE
import Theorems.Thm_ULHC_pair_flip_eq
import Theorems.Thm_ULHC_lat1_not_mem
import Theorems.Thm_ULHC_lat2_not_mem
import Theorems.Thm_ULHC_front_not_mem
import Theorems.Thm_ULHC_front_mem_next
import Theorems.Thm_ULHC_back_cellJ_succ
import Theorems.Thm_ULHC_corner_ne
import Theorems.Thm_ULHC_pat_flip_pair
import Theorems.Thm_ULHC_isCell_corners
import Theorems.Thm_ULHC_Deg2_class
import Theorems.Thm_ULHC_flipCol_succ
import Theorems.Thm_ULHC_ACell_merge
import Theorems.Thm_ULHC_APair_flip
import Theorems.Thm_ULHC_Adj_symm
import Theorems.Thm_ULHC_Conn_symm
import Theorems.Thm_ULHC_Edge_hi_mk
import Theorems.Thm_ULHC_Edge_lo_h
import Theorems.Thm_ULHC_Edge_lo_v
import Theorems.Thm_ULHC_Edge_q_h
import Theorems.Thm_ULHC_Edge_q_v
import Theorems.Thm_ULHC_Ends_merge
import Theorems.Thm_ULHC_back_nb
import Theorems.Thm_ULHC_cellJ_zero
import Theorems.Thm_ULHC_flip_eq
import Theorems.Thm_ULHC_nb_cellJ
attribute [local simp] ULHC.Edge.hi_mk
attribute [local simp] ULHC.Edge.lo_h
attribute [local simp] ULHC.Edge.lo_v
attribute [local simp] ULHC.Edge.q_h
attribute [local simp] ULHC.Edge.q_v



set_option autoImplicit true
open ULHC
open Finset Classical
variable {V : Finset Pt} {c : Pt} {s : Side}
namespace ULHC
theorem _root_.solution : ∀ k : ℕ, k % 2 = 0 → ∀ F : Finset Edge, Deg2 V F →
    (∀ j ≤ k, IsCell V (cellJ c s j)) → StripPat F c s (k + 1) →
    ¬ Conn F (back1 c s) (front1 c s) → ncomp V (flipCol F c s (k + 1)) + 1 = ncomp V F ∧
      ∀ x y, ¬ IsMid c s k x → ¬ IsMid c s k y →
        (Conn (flipCol F c s (k + 1)) x y ↔ Conn F x y ∨
          (Conn F x (back1 c s) ∧ Conn F (front1 c s) y) ∨
          (Conn F x (front1 c s) ∧ Conn F (back1 c s) y)) := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
  intro hk F hF hcell hpat hsep
  rcases (show k = 0 ∨ 2 ≤ k by omega) with rfl | hk2
  · -- One alternating cell: a merge.
    rw [flipCol_succ]
    simp only [flipCol]
    rw [cellJ_zero]
    have hc : IsCell V c := by have := hcell 0 le_rfl; rwa [cellJ_zero] at this
    obtain ⟨hb, hl, hf⟩ := hpat
    have l1 := (hl 0 (by omega)).1
    have l2 := (hl 0 (by omega)).2
    have f0 := hf 0 (by omega)
    rw [cellJ_zero] at l1 l2 f0
    simp at l1 l2 f0
    have C := mkBF c s
    rw [(mkBF c s).flip_eq (mkBF_cellE c s) hb f0 l1 l2]
    obtain ⟨cb1, cb2, cf1, cf2⟩ := isCell_corners hc s
    obtain ⟨h1, h2⟩ := (mkBF c s).merge hF.1 cb1 cf1 hb f0
      (fun z hz => by rcases hz with hz | hz
                      · exact hF.class cb1 hz
                      · exact hF.class cf1 hz) hsep
    exact ⟨h1, fun x y _ _ => h2 x y⟩
  · -- Two more cells: the pair changes nothing.
    obtain ⟨m, rfl⟩ : ∃ m, k = m + 2 := ⟨k - 2, by omega⟩
    have hm : m % 2 = 0 := by omega
    rw [show m + 2 + 1 = m + 3 from rfl, flipCol_succ, flipCol_succ]
    set u := cellJ c s (m + 1)
    have hnb : nb u s = cellJ c s (m + 2) := nb_cellJ c s (m + 1)
    obtain ⟨hb, hl, hf⟩ := hpat
    -- Memberships around the pair.
    have uL1 : lat1 u s ∈ F := (hl (m + 1) (by omega)).1.2 (by omega)
    have uL2 : lat2 u s ∈ F := (hl (m + 1) (by omega)).2.2 (by omega)
    have uF : front u s ∈ F := (hf (m + 1) (by omega)).2 (by omega)
    have uB : back u s ∉ F := by
      rw [back_cellJ_succ]
      intro h; have := (hf m (by omega)).1 h; omega
    have wL1 : lat1 (nb u s) s ∉ F := by
      rw [hnb]; intro h; have := (hl (m + 2) (by omega)).1.1 h; omega
    have wL2 : lat2 (nb u s) s ∉ F := by
      rw [hnb]; intro h; have := (hl (m + 2) (by omega)).2.1 h; omega
    have wF : front (nb u s) s ∈ F := by
      rw [hnb]; exact (hf (m + 2) (by omega)).2 (by omega)
    have hdouble : flip (flip F (cellJ c s (m + 2))) (cellJ c s (m + 1)) = (mkPair u s).res F := by
      rw [← hnb]; exact pair_flip_eq u s uL1 uL2 wF uB wL1 wL2
    have hcu : IsCell V u := hcell (m + 1) (by omega)
    have hcw : IsCell V (nb u s) := by rw [hnb]; exact hcell (m + 2) (by omega)
    obtain ⟨ub1, ub2, uf1, uf2⟩ := isCell_corners hcu s
    obtain ⟨_, _, wf1, wf2⟩ := isCell_corners hcw s
    obtain ⟨hcount, hrel⟩ := (mkPair u s).flip ub2 uf1 uf2 wf1 uL1 uL2 uF wF
      (hF.2 _ uf1) (hF.2 _ uf2)
    -- The new factor.
    rw [hdouble]
    have hF2' : Deg2 V ((mkPair u s).res F) := by
      rw [← hdouble]
      have hw : cellJ c s (m + 2) = nb u s := hnb.symm
      have d1 : Deg2 V (flip F (cellJ c s (m + 2))) := by
        rw [hw]
        exact hF.flip (mkBF (nb u s) s) hcw (mkBF_cellE _ s)
          (by show back (nb u s) s ∈ F; rw [back_nb]; exact uF) wF wL1 wL2
      have m1 : lat1 u s ∈ flip F (cellJ c s (m + 2)) := by
        rw [mem_flip_iff]; have := lat1_not_mem c s (j := m + 1) (m := m + 2) (by omega); tauto
      have m2 : lat2 u s ∈ flip F (cellJ c s (m + 2)) := by
        rw [mem_flip_iff]; have := lat2_not_mem c s (j := m + 1) (m := m + 2) (by omega); tauto
      have m3 : back u s ∉ flip F (cellJ c s (m + 2)) := by
        rw [mem_flip_iff, back_cellJ_succ]
        have := front_not_mem c s (j := m) (m := m + 2) (by omega) (by omega)
        rw [back_cellJ_succ] at uB; tauto
      have m4 : front u s ∉ flip F (cellJ c s (m + 2)) := by
        rw [mem_flip_iff]; have := front_mem_next c s (m + 1); tauto
      exact d1.flip (mkLat u s) hcu (mkLat_cellE u s) m1 m2 m3 m4
    have hpat2 : StripPat ((mkPair u s).res F) c s (m + 1) := by
      rw [← hdouble]; exact pat_flip_pair hm ⟨hb, hl, hf⟩
    have hsep2 : ¬ Conn ((mkPair u s).res F) (back1 c s) (front1 c s) := by
      obtain ⟨n1, n2, n3, n4⟩ := corner_ne c s (m := m + 1) (by omega)
      rw [hrel _ _ n1 n2 n3 n4]; exact hsep
    obtain ⟨ihc, ihr⟩ := ih m (by omega) hm _ hF2' (fun j hj => hcell j (by omega)) hpat2 hsep2
    refine ⟨by omega, fun x y hx hy => ?_⟩
    have nm : ∀ z, ¬ IsMid c s (m + 2) z → z ≠ front1 u s ∧ z ≠ front2 u s := by
      intro z hz
      exact ⟨fun h => hz ⟨m + 1, by omega, by omega, Or.inl h⟩,
        fun h => hz ⟨m + 1, by omega, by omega, Or.inr h⟩⟩
    have sub : ∀ z, ¬ IsMid c s (m + 2) z → ¬ IsMid c s m z := by
      intro z hz ⟨j, h1, h2, h3⟩; exact hz ⟨j, h1, by omega, h3⟩
    obtain ⟨n1, n2, n3, n4⟩ := corner_ne c s (m := m + 1) (by omega)
    obtain ⟨x1, x2⟩ := nm x hx
    obtain ⟨y1, y2⟩ := nm y hy
    rw [ihr x y (sub x hx) (sub y hy), hrel _ _ x1 x2 y1 y2, hrel _ _ x1 x2 n1 n2,
      hrel _ _ n3 n4 y1 y2, hrel _ _ x1 x2 n3 n4, hrel _ _ n1 n2 y1 y2]
end ULHC
