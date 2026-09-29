-- Prove2me | solution 1 for SimpleGraph.exists_walkConnected_transversal_of_preconnected
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.503601+00:00
-- url     : https://prove2.me/submissions/b2d210d0-04be-52d5-97fb-e9ec06a3ce91

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_SimpleGraph_exists_walkConnected_transversal_of_preconnected

set_option autoImplicit false

open Subgroup MulAction SimpleGraph Monoid

namespace GroupTheory

namespace GraphTransversal

def WalkConnected {V : Type*} (T : SimpleGraph V) (s : Set V) : Prop :=
  ∀ v ∈ s, ∀ w ∈ s, ∃ p : T.Walk v w, ∀ x ∈ p.support, x ∈ s

structure IsConnectedTransversal {V : Type*} (T : SimpleGraph V) (Γ : Type*) [Group Γ]
    [MulAction Γ V] (D : Set V) : Prop where

  walkConnected : WalkConnected T D

  eq_of_mem_orbit : ∀ v ∈ D, ∀ w ∈ D, v ∈ orbit Γ w → v = w

  exists_mem_orbit : ∀ u : V, ∃ v ∈ D, v ∈ orbit Γ u

variable {V : Type*} {T : SimpleGraph V} {Γ : Type*} [Group Γ] [MulAction Γ V]

theorem walkConnected_singleton (T : SimpleGraph V) (v₀ : V) : WalkConnected T {v₀} := by
  intro v hv w hw
  rw [Set.mem_singleton_iff] at hv hw
  subst hv; subst hw
  exact ⟨Walk.nil, by simp⟩

theorem WalkConnected.insert_of_adj {s : Set V} (hs : WalkConnected T s) {v w : V}
    (hv : v ∈ s) (hadj : T.Adj v w) : WalkConnected T (insert w s) := by

  have key : ∀ x ∈ insert w s, ∃ p : T.Walk v x, ∀ y ∈ p.support, y ∈ insert w s := by
    intro x hx
    rcases Set.mem_insert_iff.mp hx with rfl | hx
    · refine ⟨Walk.cons hadj Walk.nil, fun y hy => ?_⟩
      simp only [Walk.support_cons, Walk.support_nil, List.mem_cons,
        List.not_mem_nil, or_false] at hy
      rcases hy with rfl | rfl
      · exact Set.mem_insert_of_mem _ hv
      · exact Set.mem_insert _ _
    · obtain ⟨p, hp⟩ := hs v hv x hx
      exact ⟨p, fun y hy => Set.mem_insert_of_mem _ (hp y hy)⟩
  intro a ha b hb
  obtain ⟨p, hp⟩ := key a ha
  obtain ⟨q, hq⟩ := key b hb
  refine ⟨p.reverse.append q, fun y hy => ?_⟩
  rw [Walk.support_append, List.mem_append] at hy
  rcases hy with hy | hy
  · rw [Walk.support_reverse, List.mem_reverse] at hy
    exact hp y hy
  · exact hq y (List.mem_of_mem_tail hy)

theorem walkConnected_sUnion {c : Set (Set V)} (hchain : IsChain (· ⊆ ·) c)
    (hwc : ∀ s ∈ c, WalkConnected T s) : WalkConnected T (⋃₀ c) := by
  rintro v ⟨s, hs, hvs⟩ w ⟨t, ht, hwt⟩
  rcases hchain.total hs ht with hst | hts
  · obtain ⟨p, hp⟩ := hwc t ht v (hst hvs) w hwt
    exact ⟨p, fun x hx => Set.mem_sUnion.mpr ⟨t, ht, hp x hx⟩⟩
  · obtain ⟨p, hp⟩ := hwc s hs v hvs w (hts hwt)
    exact ⟨p, fun x hx => Set.mem_sUnion.mpr ⟨s, hs, hp x hx⟩⟩

private theorem mem_orbit_symm' {a b : V} (h : a ∈ orbit Γ b) : b ∈ orbit Γ a := by
  obtain ⟨γ, rfl⟩ := h
  exact ⟨γ⁻¹, inv_smul_smul γ b⟩

theorem eq_of_mem_orbit_sUnion {c : Set (Set V)} (hchain : IsChain (· ⊆ ·) c)
    (hinj : ∀ s ∈ c, ∀ v ∈ s, ∀ w ∈ s, v ∈ orbit Γ w → v = w) :
    ∀ v ∈ ⋃₀ c, ∀ w ∈ ⋃₀ c, v ∈ orbit Γ w → v = w := by
  rintro v ⟨s, hs, hvs⟩ w ⟨t, ht, hwt⟩ hvw
  rcases hchain.total hs ht with hst | hts
  · exact hinj t ht v (hst hvs) w hwt hvw
  · exact hinj s hs v hvs w (hts hwt) hvw

theorem eq_of_mem_orbit_insert {s : Set V}
    (hs : ∀ v ∈ s, ∀ w ∈ s, v ∈ orbit Γ w → v = w) {w : V}
    (hw : ¬∃ v ∈ s, v ∈ orbit Γ w) :
    ∀ v ∈ insert w s, ∀ v' ∈ insert w s, v ∈ orbit Γ v' → v = v' := by
  intro v hv v' hv' hvv'
  rcases Set.mem_insert_iff.mp hv with rfl | hvs <;>
    rcases Set.mem_insert_iff.mp hv' with rfl | hv's
  · rfl
  · exact absurd ⟨v', hv's, mem_orbit_symm' hvv'⟩ hw
  · exact absurd ⟨v, hvs, hvv'⟩ hw
  · exact hs v hvs v' hv's hvv'

theorem exists_adj_of_walk (hsmul : ∀ (γ : Γ) {v w : V}, T.Adj v w → T.Adj (γ • v) (γ • w))
    {s : Set V} {a b : V} (p : T.Walk a b) :
    (∃ v ∈ s, v ∈ orbit Γ a) → (¬∃ v ∈ s, v ∈ orbit Γ b) →
      ∃ v ∈ s, ∃ w, T.Adj v w ∧ ¬∃ v' ∈ s, v' ∈ orbit Γ w := by
  induction p with
  | nil => exact fun ha hb => absurd ha hb
  | @cons a c b hac p ih =>
    intro ha hb
    by_cases hc : ∃ v ∈ s, v ∈ orbit Γ c
    · exact ih hc hb
    · obtain ⟨v, hvs, γ, hγ⟩ := ha
      refine ⟨v, hvs, γ • c, ?_, ?_⟩
      · rw [← hγ]
        exact hsmul γ hac
      · rintro ⟨v', hv's, hv'⟩
        rw [MulAction.orbit_smul] at hv'
        exact hc ⟨v', hv's, hv'⟩

theorem exists_isConnectedTransversal
    (hsmul : ∀ (γ : Γ) {v w : V}, T.Adj v w → T.Adj (γ • v) (γ • w))
    (hpre : T.Preconnected) (v₀ : V) :
    ∃ D : Set V, v₀ ∈ D ∧ IsConnectedTransversal T Γ D := by
  classical

  obtain ⟨D, hsub, hDmem, hDmax⟩ := zorn_subset_nonempty
    {s : Set V | v₀ ∈ s ∧ WalkConnected T s ∧ ∀ v ∈ s, ∀ w ∈ s, v ∈ orbit Γ w → v = w}
    (fun c hc hchain hcne => by
      obtain ⟨s₀, hs₀⟩ := hcne
      exact ⟨⋃₀ c, ⟨Set.mem_sUnion.mpr ⟨s₀, hs₀, (hc hs₀).1⟩,
        walkConnected_sUnion hchain fun s hs => (hc hs).2.1,
        eq_of_mem_orbit_sUnion hchain fun s hs => (hc hs).2.2⟩,
        fun s hs => Set.subset_sUnion_of_mem hs⟩)
    {v₀}
    ⟨Set.mem_singleton v₀, walkConnected_singleton T v₀, by
      intro v hv w hw _
      rw [Set.mem_singleton_iff] at hv hw
      rw [hv, hw]⟩
  have hv₀D : v₀ ∈ D := hsub (Set.mem_singleton v₀)

  refine ⟨D, hv₀D, hDmem.2.1, hDmem.2.2, fun u => ?_⟩
  by_contra hu

  obtain ⟨p⟩ := hpre v₀ u
  obtain ⟨v, hvD, w, hadj, hw⟩ :=
    exists_adj_of_walk hsmul p ⟨v₀, hv₀D, MulAction.mem_orbit_self v₀⟩ hu

  have hwD : w ∉ D := fun hwD => hw ⟨w, hwD, MulAction.mem_orbit_self w⟩
  have hins : insert w D ∈
      {s : Set V | v₀ ∈ s ∧ WalkConnected T s ∧ ∀ v ∈ s, ∀ w ∈ s, v ∈ orbit Γ w → v = w} :=
    ⟨Set.mem_insert_of_mem _ hv₀D, hDmem.2.1.insert_of_adj hvD hadj,
      eq_of_mem_orbit_insert hDmem.2.2 hw⟩

  exact hwD (hDmax hins (Set.subset_insert w D) (Set.mem_insert w D))

end GraphTransversal

end GroupTheory

theorem solution {V : Type*} {T : SimpleGraph V} {Γ : Type*} [Group Γ] [MulAction Γ V]
    (hsmul : ∀ (γ : Γ) {v w : V}, T.Adj v w → T.Adj (γ • v) (γ • w))
    (hpre : T.Preconnected) (v₀ : V) :
    ∃ D : Set V, v₀ ∈ D ∧
      (∀ v ∈ D, ∀ w ∈ D, ∃ p : T.Walk v w, ∀ x ∈ p.support, x ∈ D) ∧
      (∀ v ∈ D, ∀ w ∈ D, v ∈ MulAction.orbit Γ w → v = w) ∧
      (∀ u : V, ∃ v ∈ D, v ∈ MulAction.orbit Γ u) := by
  obtain ⟨D, h0, hD⟩ := GroupTheory.GraphTransversal.exists_isConnectedTransversal hsmul hpre v₀
  exact ⟨D, h0, hD.walkConnected, hD.eq_of_mem_orbit, hD.exists_mem_orbit⟩

end S_SimpleGraph_exists_walkConnected_transversal_of_preconnected
end P2MW
export P2MW.S_SimpleGraph_exists_walkConnected_transversal_of_preconnected (solution)
