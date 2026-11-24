-- Prove2me | solution 1 for ULHC.step_cell
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T04:19:41.866852+00:00
-- url     : https://prove2.me/submissions/9210c2fb-682e-4199-ae3c-48983e14a5e8

import Definitions.Def_ULHC_StripCount
import Definitions.Def_ULHC_Walk
import Theorems.Thm_ULHC_walk_local
import Theorems.Thm_ULHC_Border_not_cut
import Theorems.Thm_ULHC_Edge_hi_mk
import Theorems.Thm_ULHC_Edge_lo_h
import Theorems.Thm_ULHC_Edge_lo_v
import Theorems.Thm_ULHC_Edge_q_h
import Theorems.Thm_ULHC_Edge_q_v
import Theorems.Thm_ULHC_outArc_eq
attribute [local simp] ULHC.Edge.hi_mk
attribute [local simp] ULHC.Edge.lo_h
attribute [local simp] ULHC.Edge.lo_v
attribute [local simp] ULHC.Edge.q_h
attribute [local simp] ULHC.Edge.q_v



set_option autoImplicit true
open ULHC
open Finset Classical
namespace ULHC
theorem _root_.solution {V : Finset Pt} {F : Finset Edge} {P : Finset Pt} (hB : Border V F P)
    (w : Pt) (o : Bool)
    (hlat : ∀ s, Cut P (sideEdge w s) → sideEdge w (latA s) ∈ F ∨ sideEdge w (latB s) ∈ F)
    (halt : Alt F w → ∀ s, ¬ Cut P (sideEdge w s))
    (si : Side) (hcut : Cut P (sideEdge w si)) (hin : outArc F w si = !o) :
    (∃ so, so ≠ si ∧ Cut P (sideEdge w so) ∧ outArc F w so = o ∧
        ∀ s', Cut P (sideEdge w s') → outArc F w s' = !o → s' = si) ∨
    (∃ d, sideEdge w d ∈ F ∧ sideEdge w d.opp ∉ F ∧ sideEdge w (latA d) ∉ F ∧
        sideEdge w (latB d) ∉ F ∧ (si = latA d ∨ si = latB d) ∧ ¬ Cut P (sideEdge w d.opp) ∧
        outArc F w d.opp = o ∧ ∀ s, Cut P (sideEdge w s) → outArc F w s = !o) := by
  obtain ⟨x, y⟩ := w
  set mb := decide (bot (x, y) ∈ F)
  set mt := decide (top (x, y) ∈ F)
  set ml := decide (lft (x, y) ∈ F)
  set mr := decide (rgt (x, y) ∈ F)
  set pbl := decide ((x, y) ∈ P)
  set pbr := decide ((x + 1, y) ∈ P)
  set ptl := decide ((x, y + 1) ∈ P)
  set ptr := decide ((x + 1, y + 1) ∈ P)
  have hm : ∀ s, mS mb mt ml mr s = true ↔ sideEdge (x, y) s ∈ F := by
    intro s; cases s <;> simp [mS, mb, mt, ml, mr, sideEdge]
  have hc : ∀ s, cutS pbl pbr ptl ptr s = true ↔ Cut P (sideEdge (x, y) s) := by
    intro s
    cases s <;> simp only [cutS, Cut, sideEdge, bot, top, lft, rgt, Edge.q, pbl, pbr, ptl, ptr]
    · by_cases h1 : (x, y) ∈ P <;> by_cases h2 : (x + 1, y) ∈ P <;> simp [h1, h2]
    · by_cases h1 : (x, y + 1) ∈ P <;> by_cases h2 : (x + 1, y + 1) ∈ P <;> simp [h1, h2]
    · by_cases h1 : (x, y) ∈ P <;> by_cases h2 : (x, y + 1) ∈ P <;> simp [h1, h2]
    · by_cases h1 : (x + 1, y) ∈ P <;> by_cases h2 : (x + 1, y + 1) ∈ P <;> simp [h1, h2]
  have hmf : ∀ s, mS mb mt ml mr s = false ↔ sideEdge (x, y) s ∉ F := by
    intro s; rw [← hm s]; simp
  have hcf : ∀ s, cutS pbl pbr ptl ptr s = false ↔ ¬ Cut P (sideEdge (x, y) s) := by
    intro s; rw [← hc s]; simp
  have ho : ∀ s, outS (par (x, y)) (mS mb mt ml mr) s = outArc F (x, y) s := by
    intro s
    rw [outArc_eq]
    cases s <;> rfl
  have key := walk_local mb mt ml mr pbl pbr ptl ptr (par (x, y)) o si
    (fun s hs => (hcf s).2 (hB.not_cut ((hm s).1 hs)))
    (by
      intro s hs
      rcases hlat s ((hc s).1 hs) with h | h
      · rw [(hm _).2 h]; rfl
      · rw [(hm _).2 h]; simp)
    (by
      intro h s
      apply (hcf s).2
      apply halt _ s
      simp only [Bool.and_eq_true, beq_iff_eq, bne_iff_ne, ne_eq] at h
      obtain ⟨⟨h1, h2⟩, h3⟩ := h
      unfold Alt
      simp only [mb, mt, ml, mr] at h1 h2 h3
      by_cases hb : bot (x, y) ∈ F <;> by_cases hl : lft (x, y) ∈ F <;> simp_all)
    ((hc si).2 hcut)
    (by rw [ho]; exact hin)
  rcases key with ⟨so, h1, h2, h3, h4⟩ | ⟨d, h1, h2, h3, h4, h5, h6, h7, h8⟩
  · left
    refine ⟨so, h1, (hc so).1 h2, by rw [← ho]; exact h3, ?_⟩
    intro s' hs' ho'
    exact h4 s' ((hc s').2 hs') (by rw [ho]; exact ho')
  · right
    exact ⟨d, (hm d).1 h1, (hmf _).1 h2, (hmf _).1 h3, (hmf _).1 h4, h5, (hcf _).1 h6,
      by rw [← ho]; exact h7, fun s hs => by rw [← ho]; exact h8 s ((hc s).2 hs)⟩
end ULHC
