-- Prove2me | solution 1 for ULHC.separation
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T04:45:57.113456+00:00
-- url     : https://prove2.me/submissions/0a4d8d84-3195-4fbd-8193-7ca2050a3ddb

import Definitions.Def_ULHC_V2
import Definitions.Def_ULHC_Chain
import Theorems.Thm_ULHC_Edge_eq_of_ends
import Theorems.Thm_ULHC_mem_GE
import Theorems.Thm_ULHC_lift_conn
import Theorems.Thm_ULHC_bit_unique
import Theorems.Thm_ULHC_Conn_trans
import Theorems.Thm_ULHC_Edge_hi_mk
import Theorems.Thm_ULHC_Edge_lo_h
import Theorems.Thm_ULHC_Edge_lo_v
import Theorems.Thm_ULHC_Edge_q_h
import Theorems.Thm_ULHC_Edge_q_v
import Theorems.Thm_ULHC_Good_step
import Theorems.Thm_ULHC_NoTypeIII_at
attribute [local simp] ULHC.Edge.hi_mk
attribute [local simp] ULHC.Edge.lo_h
attribute [local simp] ULHC.Edge.lo_v
attribute [local simp] ULHC.Edge.q_h
attribute [local simp] ULHC.Edge.q_v



set_option autoImplicit true
open ULHC
open Finset Classical
variable {V : Finset Pt} (B : Finset Edge)
variable (hs : Solid V) (heven : ∀ c, IsCell V c → sidesIn B c % 2 = 0)
include hs heven
namespace ULHC
theorem _root_.solution {F : Finset Edge} (hFV : Inside V F) (hBF : ∀ e ∈ B, e ∉ F)
    (x0 : Pt) (hconn : ∀ z ∈ V, Conn (GE V) x0 z) :
    ∃ P : Finset Pt, Border V F P ∧ ∀ e, IsEdge V e → (Cut P e ↔ e ∈ B) := by
  let P := V.filter (fun z => Relation.ReflTransGen (PStep V B) (x0, false) (z, false))
  have bitOf : ∀ z ∈ V, ∃ b, Relation.ReflTransGen (PStep V B) (x0, false) (z, b) :=
    fun z hz => lift_conn B (hconn z hz) false
  have memP : ∀ z ∈ V, ∀ b, Relation.ReflTransGen (PStep V B) (x0, false) (z, b) →
      (z ∈ P ↔ b = false) := by
    intro z hz b hb
    simp only [P, Finset.mem_filter]
    constructor
    · rintro ⟨_, h⟩; exact bit_unique B hs heven hb h
    · rintro rfl; exact ⟨hz, hb⟩
  have step : ∀ e, IsEdge V e → ∀ b, Relation.ReflTransGen (PStep V B) (x0, false) (e.p, b) →
      Relation.ReflTransGen (PStep V B) (x0, false) (e.q, b ^^ decide (e ∈ B)) := by
    intro e he b hb
    have hadj : Adj (GE V) e.p e.q := ⟨e, mem_GE.2 he, Or.inl ⟨rfl, rfl⟩⟩
    have hiff : (∃ e' ∈ B, Ends e' e.p e.q) ↔ e ∈ B :=
      ⟨fun ⟨e', he', h⟩ => by rwa [Edge.eq_of_ends h (Or.inl ⟨rfl, rfl⟩)] at he',
        fun h => ⟨e, h, Or.inl ⟨rfl, rfl⟩⟩⟩
    have := hb.tail (show PStep V B (e.p, b) (e.q, b ^^ decide (∃ e' ∈ B, Ends e' e.p e.q)) from
      ⟨hadj, rfl⟩)
    simpa only [hiff] using this
  refine ⟨P, ⟨Finset.filter_subset _ _, ?_⟩, ?_⟩
  · intro x hx y hxy
    obtain ⟨f, hf, hfe⟩ := hxy
    have hxV : x ∈ V := Finset.mem_of_mem_filter _ hx
    obtain ⟨b, hb⟩ := bitOf x hxV
    have hb0 : b = false := (memP x hxV b hb).1 hx
    have hfB : f ∉ B := hBF f |> fun h hf' => h hf' hf
    rcases hfe with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · have hfp : Relation.ReflTransGen (PStep V B) (x0, false) (f.p, b) := by rw [h1]; exact hb
      have := step f (hFV f hf) b hfp
      rw [h2] at this
      simp only [hfB, decide_false, Bool.xor_false] at this
      exact (memP y (by rw [← h2]; exact (hFV f hf).2) b this).2 hb0
    · have hfq : Relation.ReflTransGen (PStep V B) (x0, false) (f.q, b) := by rw [h2]; exact hb
      obtain ⟨b', hb'⟩ := bitOf f.p (hFV f hf).1
      have := step f (hFV f hf) b' hb'
      simp only [hfB, decide_false, Bool.xor_false] at this
      have : b' = b := bit_unique B hs heven this hfq
      rw [h1] at hb'
      exact (memP y (by rw [← h1]; exact (hFV f hf).1) b' hb').2 (this.trans hb0)
  · intro e he
    obtain ⟨b, hb⟩ := bitOf e.p he.1
    have hq := step e he b hb
    unfold Cut
    rw [memP e.p he.1 b hb, memP e.q he.2 _ hq]
    by_cases heB : e ∈ B <;> cases b <;> simp [heB]
end ULHC
