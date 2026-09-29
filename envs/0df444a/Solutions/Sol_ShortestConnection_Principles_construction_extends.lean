-- Prove2me | solution 1 for ShortestConnection.Principles.construction_extends
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-29T03:58:57.693755+00:00
-- url     : https://prove2.me/submissions/e343192c-da63-4530-ae93-de01440b0b87

import Mathlib
import Definitions.Def_ShortestConnection_Principles_SpanningSubtree
import Definitions.Def_ShortestConnection_Principles_Construction

namespace ShortestConnection.Principles

theorem aux_ce_not_connected {V : Type*} [Fintype V] [DecidableEq V] (F : Finset (Sym2 V))
    (hF : F.card + 1 < Fintype.card V) : ¬ (linkGraph F).Connected := by
  intro h
  have h1 := h.card_vert_le_card_edgeSet_add_one
  have hsub : (linkGraph F).edgeSet ⊆ (F : Set (Sym2 V)) := by
    simp only [linkGraph, SimpleGraph.edgeSet_fromEdgeSet]
    exact Set.sdiff_subset
  have h2 : Nat.card (linkGraph F).edgeSet ≤ F.card := by
    calc Nat.card (linkGraph F).edgeSet ≤ Nat.card (F : Set (Sym2 V)) :=
          Nat.card_mono (Set.toFinite _) hsub
      _ = F.card := by simp
  rw [Nat.card_eq_fintype_card] at h1
  omega

theorem aux_ce_app {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (hG : G.Connected) (w : Sym2 V → ℝ) (F : Finset (Sym2 V))
    (hF : F.card + 1 < Fintype.card V) : ∃ e, IsApplication G w F e := by
  classical
  by_cases hiso : ∃ t : V, ∀ x, ¬ (linkGraph F).Adj t x
  · obtain ⟨t, ht⟩ := hiso
    have hne : ∃ n, G.Adj t n := by
      obtain ⟨v, hv⟩ : ∃ v, v ≠ t := by
        by_contra hc
        push_neg at hc
        have : Fintype.card V ≤ 1 :=
          Fintype.card_le_one_iff.mpr (fun a b => (hc a).trans (hc b).symm)
        omega
      obtain ⟨p⟩ := hG.preconnected t v
      cases p with
      | nil => exact absurd rfl hv
      | cons h _ => exact ⟨_, h⟩
    let S := Finset.univ.filter (fun n => G.Adj t n)
    have hS : S.Nonempty := by
      obtain ⟨n, hn⟩ := hne
      exact ⟨n, by simp [S, hn]⟩
    obtain ⟨n, hnS, hmin⟩ := S.exists_min_image (fun n => w s(t, n)) hS
    refine ⟨s(t, n), Or.inl ⟨t, n, ht, ?_, rfl, ?_⟩⟩
    · simpa [S] using hnS
    · intro m hm
      exact hmin m (by simp [S, hm])
  · push_neg at hiso
    have hnc := aux_ce_not_connected F hF
    have hex : ∃ u v, ¬ (linkGraph F).Reachable u v := by
      by_contra hc
      push_neg at hc
      have : Nonempty V := hG.nonempty
      exact hnc ⟨hc⟩
    obtain ⟨u, v, huv⟩ := hex
    obtain ⟨q⟩ := hG.preconnected u v
    obtain ⟨d, -, hd1, hd2⟩ :=
      q.exists_boundary_dart {x | (linkGraph F).Reachable u x}
        (SimpleGraph.Reachable.refl u) huv
    let T := Finset.univ.filter (fun p : V × V => (linkGraph F).Reachable u p.1 ∧
      ¬ (linkGraph F).Reachable u p.2 ∧ G.Adj p.1 p.2)
    have hT : T.Nonempty := ⟨(d.fst, d.snd), by
      simp only [T, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨hd1, hd2, d.adj⟩⟩
    obtain ⟨⟨a, b⟩, habT, hmin⟩ := T.exists_min_image (fun p => w s(p.1, p.2)) hT
    simp only [T, Finset.mem_filter, Finset.mem_univ, true_and] at habT
    obtain ⟨hua, hub, hab⟩ := habT
    refine ⟨s(a, b), Or.inr ⟨a, b, hiso a, ?_, hab, rfl, ?_⟩⟩
    · intro h
      exact hub (hua.trans h)
    · intro u' n' h1 h2 h3
      exact hmin (u', n') (by
        simp only [T, Finset.mem_filter, Finset.mem_univ, true_and]
        exact ⟨hua.trans h1, fun h => h2 (hua.symm.trans h), h3⟩)

end ShortestConnection.Principles

open ShortestConnection.Principles

theorem solution {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (hG : G.Connected) (w : Sym2 V → ℝ) (l : List (Sym2 V))
    (hl : IsConstruction G w l) (hlen : l.length < Fintype.card V - 1) :
    ∃ e : Sym2 V, IsConstruction G w (l ++ [e]) := by
  have hF : l.toFinset.card + 1 < Fintype.card V := by
    have := List.toFinset_card_le l
    omega
  obtain ⟨e, he⟩ := aux_ce_app G hG w l.toFinset hF
  refine ⟨e, ?_⟩
  intro i hi
  have hi' : i < l.length + 1 := by simpa using hi
  rcases Nat.lt_succ_iff_lt_or_eq.mp hi' with h | h
  · have := hl i h
    rw [List.take_append_of_le_length h.le, List.getElem_append_left h]
    exact this
  · subst h
    simpa using he
