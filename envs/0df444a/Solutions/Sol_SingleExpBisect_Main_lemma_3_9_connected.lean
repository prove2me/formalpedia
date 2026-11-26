-- Prove2me | solution 1 for SingleExpBisect.Main.lemma_3_9_connected
-- status  : ACCEPTED   (prove)
-- author  : @Soh Kumabe
-- created : 2026-11-26T09:23:45.652022+00:00
-- url     : https://prove2.me/submissions/b4877524-b56c-4071-af40-a3815e216c43

/- Cut-edge membership and minimum bound adapted from Secousses, Prove2Me submission 797eedb1-a223-4590-b528-4b3d16d0ab3c (Apache-2.0). -/
import Mathlib
import Definitions.Def_SingleExpBisect_Main_NodeData
import Definitions.Def_SingleExpBisect_Main_Graphs
import Theorems.Thm_SingleExpBisect_Main_lemma_3_7

set_option autoImplicit false

open scoped Classical

open SingleExpBisect.Main

open MinBisectFPT

private lemma mem_cutEdges_mk {n : ℕ} (H : SimpleGraph (Fin n)) (X : Finset (Fin n)) (a b : Fin n) :
    s(a, b) ∈ cutEdges H X ↔ H.Adj a b ∧ ((a ∈ X ∧ b ∉ X) ∨ (b ∈ X ∧ a ∉ X)) := by
  simp only [cutEdges, Finset.mem_filter, Finset.mem_univ, true_and, SimpleGraph.mem_edgeSet,
    Sym2.eq_iff]
  constructor
  · rintro ⟨hadj, u, hu, v, hv, (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)⟩
    · exact ⟨hadj, Or.inl ⟨hu, hv⟩⟩
    · exact ⟨hadj, Or.inr ⟨hu, hv⟩⟩
  · rintro ⟨hadj, (⟨ha, hb⟩ | ⟨hb, ha⟩)⟩
    · exact ⟨hadj, a, ha, b, hb, Or.inl ⟨rfl, rfl⟩⟩
    · exact ⟨hadj, b, hb, a, ha, Or.inr ⟨rfl, rfl⟩⟩

private lemma mu_le {n : ℕ} (G : SimpleGraph (Fin n)) (W S A : Finset (Fin n)) (h : A ∩ W = S) :
    mu G W S ≤ cutSize G A :=
  Nat.sInf_le ⟨A, h, rfl⟩

private lemma comp_closed {n : ℕ} {G : SimpleGraph (Fin n)} {X K : Finset (Fin n)}
    (hc : IsComponent G X K) {u v : Fin n} (hu : u ∈ K) (hv : v ∈ X) (ha : G.Adj u v) : v ∈ K := by
  classical
  have H : (G.induce ((K : Set (Fin n)) ∪ {v})).Connected := by
    apply SimpleGraph.connected_induce_union hc.2.1.preconnected _ hu (Set.mem_singleton v) ha
    exact SimpleGraph.Preconnected.of_subsingleton
  have HH : (G.induce (↑(insert v K) : Set (Fin n))).Connected := by
    have hset : (↑(insert v K) : Set (Fin n)) = (K : Set _) ∪ {v} := by ext; simp [or_comm]
    rw [hset]
    exact H
  have hx : insert v K ⊆ X := Finset.insert_subset hv hc.1
  have he := hc.2.2 (insert v K) (Finset.subset_insert _ _) hx HH
  exact he ▸ Finset.mem_insert_self v K

private lemma remove_component {n : ℕ} {G : SimpleGraph (Fin n)} (hG : G.Connected)
    {X K : Finset (Fin n)} (hK : IsComponent G X K)
    (hproper : ∃ v, v ∉ K) :
    cutSize G (X \ K) < cutSize G X := by
  classical
  obtain ⟨⟨z,hz⟩⟩ := hK.2.1.nonempty
  obtain ⟨w,hw⟩ := hproper
  obtain ⟨p⟩ := hG z w
  obtain ⟨e,he,heu,hev⟩ := p.exists_boundary_dart (K : Set _) hz hw
  have hout : e.snd ∉ X := fun hv => hev (comp_closed hK heu hv e.adj)
  have hsub : cutEdges G (X \ K) ⊆ cutEdges G X := by
    intro edge
    induction edge using Sym2.ind with
    | _ a b =>
      simp only [mem_cutEdges_mk, Finset.mem_sdiff]
      intro ⟨ha, hed⟩
      refine ⟨ha, ?_⟩
      by_cases ax : a ∈ X <;> by_cases bx : b ∈ X <;> try tauto
      have aK := fun h => comp_closed hK h bx ha
      have bK := fun h => comp_closed hK h ax ha.symm
      tauto
  have huse : s(e.fst, e.snd) ∈ cutEdges G X :=
    (mem_cutEdges_mk ..).mpr ⟨e.adj, Or.inl ⟨hK.1 heu, hout⟩⟩
  have hno : s(e.fst, e.snd) ∉ cutEdges G (X \ K) := by
    simp only [mem_cutEdges_mk, Finset.mem_sdiff]
    tauto
  exact Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨hsub, fun heq => hno (heq ▸ huse)⟩)

theorem solution {n : ℕ} (G : SimpleGraph (Fin n)) (hG : G.Connected)
    (T : RootedTD n) (k : ℕ) (hT : IsSec3Decomp G T k) (t : Fin T.N)
    (S : Finset (Fin n)) (hS : S ⊆ T.cone t) (K : Finset (Fin n))
    (hK : IsComponent G (Phi G (T.cone t) S) K) : (K ∩ T.cone t).Nonempty := by
  classical
  let W := T.cone t
  let X := Phi G W S
  have hm : X ∩ W = S ∧ cutSize G X = mu G W S := (SingleExpBisect.Main.lemma_3_7 G W S hS).1
  by_contra h
  have hd : ∀ v ∈ W, v ∉ K := fun v hw hk => h ⟨v, Finset.mem_inter.mpr ⟨hk,hw⟩⟩
  have hn : 0 < n := (Fin.pos_iff_nonempty).mpr hG.nonempty
  obtain ⟨v,hv⟩ := hT.2.2.2.2 hn t
  have hW : v ∈ W := Finset.mem_filter.mpr ⟨Finset.mem_univ _, t, Relation.ReflTransGen.refl, hv⟩
  have heq : (X \ K) ∩ W = S := by
    rw [←hm.1]
    ext x
    simp only [Finset.mem_inter, Finset.mem_sdiff]
    constructor <;> aesop
  have hs := remove_component hG hK ⟨v,hd v hW⟩
  have hb := mu_le G W S (X \ K) heq
  change cutSize G (X \ K) < cutSize G X at hs
  omega
