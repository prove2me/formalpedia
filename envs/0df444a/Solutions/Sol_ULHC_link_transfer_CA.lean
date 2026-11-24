-- Prove2me | solution 1 for ULHC.link_transfer_CA
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T05:08:19.432305+00:00
-- url     : https://prove2.me/submissions/3960307d-578c-4207-b55f-040b5ee5e43b

import Definitions.Def_ULHC_NearLemma
import Definitions.Def_ULHC_ChainLinks
import Theorems.Thm_ULHC_frame_ne
import Theorems.Thm_ULHC_inter_unique
import Theorems.Thm_ULHC_chain_lat
import Theorems.Thm_ULHC_chain_sig
import Theorems.Thm_ULHC_chain_conn
import Theorems.Thm_P2M_ULHC_alt_corners_conn__04780e54d852
import Theorems.Thm_ULHC_APair_flip
import Theorems.Thm_ULHC_Edge_hi_mk
import Theorems.Thm_ULHC_Edge_lo_h
import Theorems.Thm_ULHC_Edge_lo_v
import Theorems.Thm_ULHC_Edge_q_h
import Theorems.Thm_ULHC_Edge_q_v
import Theorems.Thm_ULHC_NoTypeIII_at
import Theorems.Thm_ULHC_alt_of_lats
import Theorems.Thm_ULHC_cellE_frame
import Theorems.Thm_ULHC_cellJ_zero
import Theorems.Thm_ULHC_deg2_flipCol
import Theorems.Thm_ULHC_end_same
import Theorems.Thm_ULHC_frame_of_allConn
import Theorems.Thm_ULHC_mem_flipCol
import Theorems.Thm_ULHC_mem_flip_off
import Theorems.Thm_ULHC_nOn_zero
import Theorems.Thm_ULHC_osi_far
import Theorems.Thm_ULHC_osi_split
import Theorems.Thm_ULHC_stripPat_congr
attribute [local simp] ULHC.Edge.hi_mk
attribute [local simp] ULHC.Edge.lo_h
attribute [local simp] ULHC.Edge.lo_v
attribute [local simp] ULHC.Edge.q_h
attribute [local simp] ULHC.Edge.q_v



set_option autoImplicit true
open ULHC
open Finset
variable {V : Finset Pt} {G : Finset Edge} (hG : Deg2 V G) (hT : NoTypeIII V G)
  {a : StripSpec} (ha : ValidStrip V G a) (hae : a.n % 2 = 0) (ha2 : 2 ≤ a.n)
  (hT' : NoTypeIII V (applyS G a))
include hG hT ha hae ha2 hT'
namespace ULHC
theorem _root_.solution {σ τ : StripSpec} (hσ : EndOK V G σ) (hev : σ.n % 2 = 0)
    (hl : CR2 V G σ τ) (hok : ChainOK σ τ) (hfl : FarLinkCA G a σ τ) :
    CR2 V (applyS G a) σ τ := by
  obtain ⟨f1, f2, f3, f4, f5, f6, f7⟩ := hfl
  obtain ⟨h2, hev', hc1, hpatc, hcellc, hoff, hne, hendc, hm1, hm2, hxy, hsplit⟩ := hl
  obtain ⟨k, hk⟩ : ∃ k, a.n = k + 2 := ⟨a.n - 2, by omega⟩
  obtain ⟨_, hpata, hcella, hsepa⟩ := ha
  have hpata' := hpata
  have hend : endCell a = cellJ a.c a.s (k + 1) := by unfold endCell; rw [hk]; rfl
  rw [hk] at hpata f1 f2 f3 f4 f5 f6
  have hcellk : ∀ j < k + 2, IsCell V (cellJ a.c a.s j) := by rw [← hk]; exact hcella
  rw [hend] at f7
  have hcella' : ∀ j ≤ k + 1, IsCell V (cellJ a.c a.s j) := fun j hj => hcellk j (by omega)
  have hk2 : k % 2 = 0 := by omega
  have hsame := end_same hT hk2 hcella' hpata
  have hT'' : NoTypeIII V (flipCol G a.c a.s (k + 2)) := by
    unfold applyS at hT'; rwa [hk] at hT'
  obtain ⟨hu, lu1, lu2, bu, fu⟩ := hσ hev
  have hsu : Conn G (back1 (endCell σ) σ.s) (back2 (endCell σ) σ.s) := by
    have hall : AllConn G (endCell σ) := by
      unfold AllConn; exact alt_corners_conn' (V := V) (hT _ hu) (alt_of_lats lu1 lu2 bu fu)
    exact (frame_of_allConn hall σ.s).1
  have hm2' : ¬ IsMid a.c a.s k (back1 (endCell σ) σ.s) := by simpa using f2
  have hm3' : ¬ IsMid a.c a.s k (back2 (endCell σ) σ.s) := by simpa using f3
  have hx' : ¬ IsMid a.c a.s k (back1 τ.c τ.s) := by simpa using f5
  have hy' : ¬ IsMid a.c a.s k (front1 τ.c τ.s) := by simpa using f6
  have hfar' : ∀ j ≤ k + 1, ∀ e ∈ cellE (endCell σ), e ∉ cellE (cellJ a.c a.s j) :=
    fun j hj e he => f1 j (by omega) e he
  -- Sides of `τ` and of `σ`'s end cell are not sides of `a`'s cells.
  --
  have hkeepτ : ∀ i < τ.n, ∀ e ∈ cellE (cellJ τ.c τ.s i), (e ∈ applyS G a ↔ e ∈ G) := by
    intro i hi e he
    unfold applyS; rw [hk, mem_flipCol, nOn_zero a.c a.s (fun j hj => f4 i hi j (by omega) e he)]
    simp
  have hpat' : StripPat (flip (applyS G a) (endCell σ)) τ.c τ.s τ.n := by
    obtain ⟨n, hn⟩ : ∃ n, τ.n = n + 1 := ⟨τ.n - 1, by omega⟩
    rw [hn] at hpatc ⊢
    refine (stripPat_congr (fun i hi e he => ?_)).2 hpatc
    rw [mem_flip_iff, mem_flip_iff, hkeepτ i (by omega) e he]
  have hsplit' : ¬ Conn (flip (applyS G a) (endCell σ)) (back1 τ.c τ.s) (front1 τ.c τ.s) := by
    unfold applyS; rw [hk]
    exact osi_split hG hk2 hcella' hpata hsepa hsame hT'' hu lu1 lu2 bu fu hsu hfar' hm2' hm3'
      hxy hsplit hx' hy'
  have hconn' : Conn (applyS G a) (back1 τ.c τ.s) (front1 τ.c τ.s) := by
    by_cases hnc : NoChain σ τ
    · have hosi := osi_far hG hk2 hcella' hpata hsepa hsame hT'' hu lu1 lu2 bu fu hsu hfar'
        hm2' hm3' hxy hsplit hx' hy'
      unfold applyS; rw [hk]
      rcases hosi with h | h
      · exact h.1
      · exact absurd ⟨hxy, h⟩ (f7 hnc)
    · -- A chain link: the start pair is joined through the shared side.
      --
      unfold NoChain at hnc
      push Not at hnc
      obtain ⟨j, hj, x, hx, hxu⟩ := hnc
      obtain ⟨rfl, hxl⟩ := hok j hj x hx hxu
      rw [cellJ_zero] at hx
      have hxlat := chain_lat ⟨h2, hev', hc1, hpatc, hcellc, hoff, hne, hendc, hm1, hm2, hxy,
        hsplit⟩ hok ⟨lu1, lu2⟩ hx hxu
      have hxG : x ∈ G := by rcases hxl with rfl | rfl; exacts [lu1, lu2]
      have hsig := chain_sig ⟨h2, hev', hc1, hpatc, hcellc, hoff, hne, hendc, hm1, hm2, hxy,
        hsplit⟩ hok
      have hc0 : ∀ e ∈ cellE τ.c, (e ∈ applyS G a ↔ e ∈ G) := fun e he =>
        hkeepτ 0 hc1 e (by rw [cellJ_zero]; exact he)
      have hsig' : SigFrom (applyS G a) τ.c τ.s τ.n 1 := by
        intro i hi hin
        have mem : ∀ y, y = lat1 (cellJ τ.c τ.s i) τ.s ∨ y = lat2 (cellJ τ.c τ.s i) τ.s ∨
            y = back (cellJ τ.c τ.s i) τ.s ∨ y = front (cellJ τ.c τ.s i) τ.s →
            y ∈ cellE (cellJ τ.c τ.s i) := by
          intro y hy; rw [cellE_frame _ τ.s]; rcases hy with rfl | rfl | rfl | rfl <;> simp
        obtain ⟨g1, g2, gb, gf⟩ := hsig i hi hin
        rw [← hkeepτ i hin _ (mem _ (Or.inl rfl))] at g1
        rw [← hkeepτ i hin _ (mem _ (Or.inr (Or.inl rfl)))] at g2
        rw [← hkeepτ i hin _ (mem _ (Or.inr (Or.inr (Or.inl rfl))))] at gb
        rw [← hkeepτ i hin _ (mem _ (Or.inr (Or.inr (Or.inr rfl))))] at gf
        exact ⟨g1, g2, gb, gf⟩
      have memc : ∀ y, y = lat1 τ.c τ.s ∨ y = lat2 τ.c τ.s ∨ y = back τ.c τ.s ∨
          y = front τ.c τ.s → y ∈ cellE τ.c := by
        intro y hy; rw [cellE_frame _ τ.s]; rcases hy with rfl | rfl | rfl | rfl <;> simp
      -- At the start cell, sides other than `x` keep their pattern value in `G`.
      --
      have hne0 : τ.c ≠ endCell σ := by
        have := hne 0 hc1; rwa [cellJ_zero] at this
      have hother : ∀ y ∈ cellE τ.c, y ≠ x → (y ∈ flip G (endCell σ) ↔ y ∈ G) :=
        fun y hy hyx => mem_flip_off (fun hyu => hyx (inter_unique hne0 hy hyu hx hxu))
      obtain ⟨n1, n2, n3, n4, _, _⟩ := frame_ne τ.c τ.s
      have hbx : back τ.c τ.s ≠ x := by rcases hxlat with rfl | rfl; exacts [n1, n2]
      have hfx : front τ.c τ.s ≠ x := by rcases hxlat with rfl | rfl; exacts [n3, n4]
      have hb0 : back τ.c τ.s ∈ applyS G a := by
        rw [hc0 _ (memc _ (Or.inr (Or.inr (Or.inl rfl)))),
          ← hother _ (memc _ (Or.inr (Or.inr (Or.inl rfl)))) hbx]
        exact hpatc.1
      have hf0 : front τ.c τ.s ∈ applyS G a ↔ τ.n = 1 := by
        rw [hc0 _ (memc _ (Or.inr (Or.inr (Or.inr rfl)))),
          ← hother _ (memc _ (Or.inr (Or.inr (Or.inr rfl)))) hfx]
        have := hpatc.2.2 0 hc1
        rw [cellJ_zero] at this
        rw [this]; omega
      have hx0 : lat1 τ.c τ.s ∈ applyS G a ∨ lat2 τ.c τ.s ∈ applyS G a := by
        rcases hxlat with h | h
        · left; rw [← h, hc0 _ hx]; exact hxG
        · right; rw [← h, hc0 _ hx]; exact hxG
      have hGa : Deg2 V (applyS G a) := by
        unfold applyS; exact deg2_flipCol _ G hG hpata' hcella
      exact chain_conn hGa hT' hc1 hsig' (fun h => hcellc 1 (by omega)) hb0 hf0 hx0
  exact ⟨h2, hev', hc1, hpat', hcellc, hoff, hne, hendc, hm1, hm2, hconn', hsplit'⟩
end ULHC
