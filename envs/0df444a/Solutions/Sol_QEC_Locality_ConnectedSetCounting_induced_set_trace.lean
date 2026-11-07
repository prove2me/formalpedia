-- Prove2me | solution 1 for QEC.Locality.ConnectedSetCounting.induced_set_trace
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T11:45:43.143169+00:00
-- url     : https://prove2.me/submissions/775c6ac9-b7e0-4334-af26-284bb7b352e4

import Definitions.Def_QEC_Locality_Graph_Core
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Definitions.Def_QEC_Locality_Graph_ConnectedSetCounting
section
noncomputable section
namespace QEC.Locality.ConnectedSetCounting
open Classical
open scoped BigOperators
universe u v
variable {V : Type u} [Fintype V] [DecidableEq V]
private theorem mem_next (G : SimpleGraph V) (r w : V) :
    w ∈ next G r ↔ w = r ∨ G.Adj r w := by
  classical
  simp [next]
private theorem mem_traces_succ (G : SimpleGraph V) (r : V) (n : Nat) (l : List V) :
    l ∈ traces G r (n+1) ↔
      ∃ w ∈ next G r, ∃ t ∈ traces G w n, r::t = l := by
  classical
  simp only [traces, Finset.mem_biUnion, Finset.mem_image]
private theorem prepend_trace (G : SimpleGraph V) {r w : V} {n : Nat} {l : List V}
    (hw : w ∈ next G r) (hl : l ∈ traces G w n) : r::l ∈ traces G r (n+1) :=
  (mem_traces_succ G r n _).mpr ⟨w,hw,l,hl,rfl⟩
private theorem root_mem_trace (G : SimpleGraph V) (r : V) (n : Nat) (l : List V)
    (hl : l ∈ traces G r n) : r ∈ l.toFinset := by
  cases n with
  | zero =>
    have he : l = [r] := by simpa [traces] using hl
    simp [he]
  | succ n =>
    obtain ⟨w,hw,t,ht,rfl⟩ := (mem_traces_succ G r n l).mp hl
    simp
private theorem map_trace {W : Type v} [Fintype W] [DecidableEq W]
    (G : SimpleGraph V) (H : SimpleGraph W) (f : V → W)
    (hf : ∀ a b, G.Adj a b → H.Adj (f a) (f b))
    (r : V) (n : Nat) (l : List V) (hl : l ∈ traces G r n) :
    l.map f ∈ traces H (f r) n := by
  induction n generalizing r l with
  | zero =>
    have he : l = [r] := by simpa [traces] using hl
    simp [he,traces]
  | succ n ih =>
    obtain ⟨w,hw,t,ht,rfl⟩ := (mem_traces_succ G r n l).mp hl
    have hw' : f w ∈ next H (f r) := by
      rcases (mem_next G r w).mp hw with h | h
      · exact (mem_next H (f r) (f w)).mpr (Or.inl (congrArg f h))
      · exact (mem_next H (f r) (f w)).mpr (Or.inr (hf r w h))
    exact prepend_trace H hw' (ih w t ht)
private theorem insert_round_trip (G : SimpleGraph V) (n : Nat) (r : V) (l : List V)
    (hl : l ∈ traces G r n) (w z : V) (hw : w ∈ l.toFinset) (hwz : G.Adj w z) :
    ∃ l' ∈ traces G r (n+2), l'.toFinset = insert z l.toFinset := by
  induction n generalizing r l with
  | zero =>
    have he : l = [r] := by simpa [traces] using hl
    subst l
    have hwr : w = r := by simpa using hw
    subst w
    refine ⟨[r,z,r], prepend_trace G ((mem_next G r z).mpr (.inr hwz))
      (prepend_trace G ((mem_next G z r).mpr (.inr hwz.symm)) (by simp [traces])), ?_⟩
    simp [Finset.insert_comm]
  | succ n ih =>
    by_cases hwr : w = r
    · subst w
      refine ⟨r::z::l, prepend_trace G ((mem_next G r z).mpr (.inr hwz))
        (prepend_trace G ((mem_next G z r).mpr (.inr hwz.symm)) hl), ?_⟩
      have hr := root_mem_trace G r (n+1) l hl
      simp only [List.toFinset_cons]
      rw [Finset.insert_comm r z, Finset.insert_eq_of_mem hr]
    · obtain ⟨a,ha,t,ht,rfl⟩ := (mem_traces_succ G r n l).mp hl
      have hwt : w ∈ t.toFinset := by
        have hi : w ∈ insert r t.toFinset := by simpa only [List.toFinset_cons] using hw
        rcases Finset.mem_insert.mp hi with h | h
        · exact False.elim (hwr h)
        · exact h
      obtain ⟨t',ht',he⟩ := ih a t ht hwt
      refine ⟨r::t', prepend_trace G ha ht', ?_⟩
      simp only [List.toFinset_cons, he]
      exact Finset.insert_comm r z t.toFinset
private theorem cover_all_aux (N : Nat) :
    ∀ {V : Type u} [Fintype V] [DecidableEq V] (G : SimpleGraph V),
      Fintype.card V = N → G.Connected → ∀ r : V,
      ∃ l ∈ traces G r (2*Fintype.card V), l.toFinset = Finset.univ := by
  induction N using Nat.strong_induction_on with
  | h N ih =>
    intro V _ _ G hN hc r
    classical
    by_cases hsub : Subsingleton V
    · letI := hsub
      have hu : (Finset.univ : Finset V) = {r} := by
        ext x
        simp [Subsingleton.elim x r]
      have hcard : Fintype.card V = 1 := by
        simpa only [Finset.card_univ, Finset.card_singleton] using congrArg Finset.card hu
      refine ⟨[r,r,r], ?_, ?_⟩
      · have h0 : [r] ∈ traces G r 0 := by simp [traces]
        have h1 := prepend_trace G ((mem_next G r r).mpr (.inl rfl)) h0
        have h2 := prepend_trace G ((mem_next G r r).mpr (.inl rfl)) h1
        simpa only [hcard, Nat.mul_one] using h2
      · ext x
        simp [Subsingleton.elim x r]
    · letI : Nontrivial V := not_subsingleton_iff_nontrivial.mp hsub
      obtain ⟨T,hTG,hT⟩ := hc.exists_isTree_le
      obtain ⟨a,b,hab,ha,hb⟩ := hT.exists_ne_and_degree_eq_one
      have hleaf : ∃ z : V, z ≠ r ∧ T.degree z = 1 := by
        by_cases har : a = r
        · exact ⟨b,fun hbr => hab (har.trans hbr.symm),hb⟩
        · exact ⟨a,har,ha⟩
      obtain ⟨z,hzr,hz⟩ := hleaf
      let W : Type u := {x : V // x ≠ z}
      let H : SimpleGraph W := G.induce {z}ᶜ
      have hH : H.Connected := by
        exact (hT.connected.induce_compl_singleton_of_degree_eq_one hz).mono
          (by intro x y hxy; exact hTG hxy)
      have hlt : Fintype.card W < N := by
        rw [← hN]
        exact Fintype.card_subtype_lt (x:=z) (by simp)
      have hrz : r ≠ z := Ne.symm hzr
      obtain ⟨l,hl,hcover⟩ := ih (Fintype.card W) hlt H rfl hH ⟨r,hrz⟩
      have hm : l.map (Subtype.val : W → V) ∈ traces G r (2*Fintype.card W) :=
        map_trace H G Subtype.val (fun _ _ hxy => hxy) ⟨r,hrz⟩ _ l hl
      have hs : (l.map (Subtype.val : W → V)).toFinset = Finset.univ.erase z := by
        ext x
        simp only [List.mem_toFinset, List.mem_map, Finset.mem_erase, Finset.mem_univ,
          and_true]
        constructor
        · rintro ⟨y,hy,rfl⟩
          exact y.property
        · intro hx
          have hy : (⟨x,hx⟩ : W) ∈ l.toFinset := by rw [hcover]; exact Finset.mem_univ _
          exact ⟨⟨x,hx⟩,List.mem_toFinset.mp hy,rfl⟩
      obtain ⟨w,hzw,hwunique⟩ := SimpleGraph.degree_eq_one_iff_existsUnique_adj.mp hz
      have hwz : w ≠ z := by
        intro he
        subst w
        obtain ⟨hirr⟩ := T.loopless
        exact hirr z hzw
      have hw : w ∈ (l.map (Subtype.val : W → V)).toFinset := by
        rw [hs]
        simp [hwz]
      obtain ⟨l',hl',hs'⟩ := insert_round_trip G _ r _ hm w z hw (hTG hzw).symm
      have hcard : Fintype.card W = Fintype.card V - 1 := by
        exact (Fintype.card_subtype_compl (fun x : V => x = z)).trans
          (by rw [Fintype.card_subtype_eq])
      have hpos : 0 < Fintype.card V := Fintype.card_pos_iff.mpr ⟨r⟩
      have hlen : 2*Fintype.card W+2 = 2*Fintype.card V := by omega
      refine ⟨l',hlen ▸ hl',?_⟩
      rw [hs',hs,Finset.insert_erase (Finset.mem_univ z)]
end QEC.Locality.ConnectedSetCounting
end
end

set_option autoImplicit false
noncomputable section
open QEC QEC.Locality QEC.Locality.ConnectedSetCounting
open Classical
open scoped BigOperators
universe u v
variable {V : Type u} [Fintype V] [DecidableEq V]
namespace QEC.Locality.ConnectedSetCounting
theorem _root_.solution (G : SimpleGraph V) (A : Finset V) (r : V)
    (hr : r ∈ A) (hc : (G.induce (A : Set V)).Connected) :
    ∃ l ∈ traces G r (2*A.card), l.toFinset = A := by
  classical
  obtain ⟨l,hl,hs⟩ := cover_all_aux (Fintype.card A) (G.induce (A : Set V)) rfl hc ⟨r,hr⟩
  refine ⟨l.map Subtype.val, ?_, ?_⟩
  · have hm := map_trace (G.induce (A : Set V)) G Subtype.val
      (fun _ _ hxy => hxy) ⟨r,hr⟩ _ l hl
    have hcard : Fintype.card (A : Set V) = A.card :=
      Fintype.card_of_finset' A (fun _ => Iff.rfl)
    rw [hcard] at hm
    exact hm
  · ext x
    simp only [List.mem_toFinset, List.mem_map]
    constructor
    · rintro ⟨y,hy,rfl⟩
      exact y.property
    · intro hx
      have hy : (⟨x,hx⟩ : A) ∈ l.toFinset := by rw [hs]; exact Finset.mem_univ _
      exact ⟨⟨x,hx⟩,List.mem_toFinset.mp hy,rfl⟩
end QEC.Locality.ConnectedSetCounting
