-- Prove2me | solution 1 for ULHC.series_reduce
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T05:05:43.148599+00:00
-- url     : https://prove2.me/submissions/ad34007e-9d03-421e-bb7d-47ff8fd75aae

import Definitions.Def_ULHC_Near
import Definitions.Def_ULHC_Stacked
import Theorems.Thm_ULHC_three_le_deg
import Theorems.Thm_ULHC_Ends_adj_cases
import Theorems.Thm_ULHC_Ends_ne_at
import Theorems.Thm_ULHC_Adj_symm
import Theorems.Thm_ULHC_Conn_of_adj
import Theorems.Thm_ULHC_Conn_refl
import Theorems.Thm_ULHC_Conn_symm
import Theorems.Thm_ULHC_Conn_trans
import Theorems.Thm_ULHC_DWalk_trans
import Theorems.Thm_ULHC_Edge_hi_mk
import Theorems.Thm_ULHC_Edge_lo_h
import Theorems.Thm_ULHC_Edge_lo_v
import Theorems.Thm_ULHC_Edge_q_h
import Theorems.Thm_ULHC_Edge_q_v
import Theorems.Thm_ULHC_Ends_conn
import Theorems.Thm_ULHC_Ends_inc_iff
import Theorems.Thm_ULHC_Ends_ne
import Theorems.Thm_ULHC_Ends_swap
import Theorems.Thm_ULHC_Good_step
import Theorems.Thm_ULHC_GridIso_conn_map
import Theorems.Thm_ULHC_NoTypeIII_at
import Theorems.Thm_ULHC_PStep_symm
import Theorems.Thm_ULHC_conn_map
attribute [local simp] ULHC.Edge.hi_mk
attribute [local simp] ULHC.Edge.lo_h
attribute [local simp] ULHC.Edge.lo_v
attribute [local simp] ULHC.Edge.q_h
attribute [local simp] ULHC.Edge.q_v



set_option autoImplicit true
open ULHC
open Finset
namespace ULHC
theorem _root_.solution {A K : Finset Edge} {m1 m2 x y : Pt} {a b c d : Edge}
    (ha : Ends a x m1) (hb : Ends b m1 m2) (hc : Ends c m2 y) (hd : Ends d x y)
    (aA : a ∈ A) (bA : b ∈ A) (cA : c ∈ A) (dK : d ∈ K)
    (hxm2 : x ≠ m2) (hym1 : y ≠ m1)
    (hdeg1 : deg A m1 ≤ 2) (hdeg2 : deg A m2 ≤ 2)
    (hoff : ∀ g ∈ A, ¬ (g.p = m1 ∨ g.q = m1) → ¬ (g.p = m2 ∨ g.q = m2) → g ∈ K)
    (hK : ∀ g ∈ K, g ∈ A ∨ g = d)
    {p q : Pt} (hp1 : p ≠ m1) (hp2 : p ≠ m2) (hq1 : q ≠ m1) (hq2 : q ≠ m2) :
    Conn A p q ↔ Conn K p q := by
  -- The only edges of `A` at `m1` are `a`, `b`, and at `m2` are `b`, `c`.
  --
  have nab : a ≠ b := ha.ne_at hb hxm2
  have nbc : b ≠ c := fun h => (hc.swap.ne_at hb.swap hym1) h.symm
  have ia1 : a.p = m1 ∨ a.q = m1 := (ha.inc_iff m1).2 (Or.inr rfl)
  have ib1 : b.p = m1 ∨ b.q = m1 := (hb.inc_iff m1).2 (Or.inl rfl)
  have ib2 : b.p = m2 ∨ b.q = m2 := (hb.inc_iff m2).2 (Or.inr rfl)
  have ic2 : c.p = m2 ∨ c.q = m2 := (hc.inc_iff m2).2 (Or.inl rfl)
  have hinc : ∀ g ∈ A, ((g.p = m1 ∨ g.q = m1) ∨ (g.p = m2 ∨ g.q = m2)) →
      g = a ∨ g = b ∨ g = c := by
    intro g hg hi
    by_contra hn
    simp only [not_or] at hn
    obtain ⟨na, nb', nc⟩ := hn
    rcases hi with hi | hi
    · have := three_le_deg aA bA hg ia1 ib1 hi nab (Ne.symm na) (Ne.symm nb')
      omega
    · have := three_le_deg bA cA hg ib2 ic2 hi nbc (Ne.symm nb') (Ne.symm nc)
      omega
  constructor
  · -- Collapse `m1`, `m2` onto `x`.
    --
    intro h
    let φ : Pt → Pt := fun z => if z = m1 ∨ z = m2 then x else z
    have φx : φ x = x := by simp only [φ]; split_ifs <;> rfl
    have φ1 : φ m1 = x := by simp [φ]
    have φ2 : φ m2 = x := by simp [φ]
    have φy : φ y = y := by
      simp only [φ]; rw [if_neg (not_or.2 ⟨hym1, hc.ne.symm⟩)]
    have φz : ∀ z, z ≠ m1 → z ≠ m2 → φ z = z := fun z h1 h2 => by
      simp only [φ]; rw [if_neg (not_or.2 ⟨h1, h2⟩)]
    have step : ∀ u v, Adj A u v → Conn K (φ u) (φ v) := by
      intro u v huv
      obtain ⟨g, hg, huv⟩ := huv
      -- An edge of the path, with ends `s`, `t` already joined after collapsing.
      --
      have via : ∀ {s tf : Pt}, Ends g s tf → Conn K (φ s) (φ tf) → Conn K (φ u) (φ v) := by
        intro s tf hst hc'
        rcases hst.adj_cases huv with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · rw [h1, h2]; exact hc'
        · rw [h1, h2]; exact hc'.symm
      by_cases hi : (g.p = m1 ∨ g.q = m1) ∨ (g.p = m2 ∨ g.q = m2)
      · rcases hinc g hg hi with rfl | rfl | rfl
        · apply via ha; rw [φx, φ1]; exact Conn.refl _ _
        · apply via hb; rw [φ1, φ2]; exact Conn.refl _ _
        · apply via hc; rw [φ2, φy]; exact hd.conn dK
      · simp only [not_or] at hi
        obtain ⟨⟨n1, n2⟩, n3, n4⟩ := hi
        have hgK := hoff g hg (by rw [not_or]; exact ⟨n1, n2⟩) (by rw [not_or]; exact ⟨n3, n4⟩)
        have hu : u ≠ m1 ∧ u ≠ m2 := by
          rcases huv with ⟨h1, _⟩ | ⟨_, h2⟩
          · rw [← h1]; exact ⟨n1, n3⟩
          · rw [← h2]; exact ⟨n2, n4⟩
        have hv : v ≠ m1 ∧ v ≠ m2 := by
          rcases huv with ⟨_, h2⟩ | ⟨h1, _⟩
          · rw [← h2]; exact ⟨n2, n4⟩
          · rw [← h1]; exact ⟨n1, n3⟩
        rw [φz u hu.1 hu.2, φz v hv.1 hv.2]
        exact Conn.of_adj ⟨g, hgK, huv⟩
    have := conn_map φ step h
    rwa [φz p hp1 hp2, φz q hq1 hq2] at this
  · -- Each edge of `K` is an edge of `A`, or `d`, whose ends are joined along the path.
    --
    intro h
    have hxy : Conn A x y := ((ha.conn aA).trans (hb.conn bA)).trans (hc.conn cA)
    refine conn_map (fun z => z) (fun u v huv => ?_) h
    obtain ⟨g, hg, huv⟩ := huv
    rcases hK g hg with hgA | rfl
    · exact Conn.of_adj ⟨g, hgA, huv⟩
    · rcases hd.adj_cases huv with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · rw [h1, h2]; exact hxy
      · rw [h1, h2]; exact hxy.symm
end ULHC
