-- Prove2me | solution 1 for SecretaryWD.Graphic.random_partition_indep_acyclic
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-06T07:26:16.323874+00:00
-- url     : https://prove2.me/submissions/436cd01d-c1f0-4255-85ae-97d8e9c625bb

import Mathlib
import Definitions.Def_SecretaryWD_Graphic_GraphicMatroid
import Definitions.Def_SecretaryWD_Graphic_RandomPartition



namespace SecretaryWD.Graphic

open Classical

variable {V : Type*} [Fintype V] [DecidableEq V]

def RPInv (E : Finset (Sym2 V)) (P : Finset (Finset (Sym2 V))) : Prop :=
  IsPartitionOf E P ∧ ∀ S : Finset (Sym2 V), IsPartIndep P S → IsAcyclicSet S

lemma rp_edge_eq {e : Sym2 V} {x x' : V} (hx : x ∈ e) (hx' : x' ∈ e) (hne : x ≠ x') :
    e = s(x, x') := by
  exact (Sym2.mem_and_mem_iff hne).1 ⟨hx, hx'⟩

lemma rp_mem_redPart {E : Finset (Sym2 V)} {col : V → Bool} {x : V} {f : Sym2 V} :
    f ∈ redPart E col x ↔ f ∈ E ∧ x ∈ f ∧ ∃ y ∈ f, col y = false := by
  unfold redPart; simp [Finset.mem_filter]

lemma rp_mem_roundParts {E : Finset (Sym2 V)} {col : V → Bool} {p : Finset (Sym2 V)} :
    p ∈ roundParts E col ↔ (∃ x, col x = true ∧ redPart E col x = p) ∧ p.Nonempty := by
  unfold roundParts; simp [Finset.mem_filter, Finset.mem_image]

lemma rp_mem_blue {E : Finset (Sym2 V)} {col : V → Bool} {f : Sym2 V} :
    f ∈ blueEdges E col ↔ f ∈ E ∧ ∀ y ∈ f, col y = false := by
  unfold blueEdges; simp [Finset.mem_filter]

/-- An edge in some round part, containing a red node `x`, lies in `redPart x`. -/
lemma rp_in_redPart_of {E : Finset (Sym2 V)} {col : V → Bool} {x x' : V} {f : Sym2 V}
    (hx : col x = true) (hxf : x ∈ f) (hf : f ∈ redPart E col x') (hx' : col x' = true) :
    f ∈ redPart E col x := by
  rw [rp_mem_redPart] at hf ⊢
  obtain ⟨hfE, hx'f, y, hy, hcy⟩ := hf
  refine ⟨hfE, hxf, y, hy, hcy⟩

lemma rp_red_eq {E : Finset (Sym2 V)} {col : V → Bool} {x x' : V} {f : Sym2 V}
    (hx : col x = true) (hxf : x ∈ f) (hf : f ∈ redPart E col x') (hx' : col x' = true) :
    x = x' := by
  by_contra hne
  rw [rp_mem_redPart] at hf
  obtain ⟨_, hx'f, y, hy, hcy⟩ := hf
  have := rp_edge_eq hxf hx'f hne
  subst this
  rcases Sym2.mem_iff.1 hy with rfl | rfl <;> simp_all

lemma rp_step (E : Finset (Sym2 V)) (col : V → Bool) (Q : Finset (Finset (Sym2 V)))
    (hQ : RPInv (blueEdges E col) Q) : RPInv E (roundParts E col ∪ Q) := by
  obtain ⟨⟨hQa, hQb⟩, hQc⟩ := hQ
  have hblueE : blueEdges E col ⊆ E := fun f hf => (rp_mem_blue.1 hf).1
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · intro p hp
    rcases Finset.mem_union.1 hp with hp | hp
    · obtain ⟨⟨x, hx, rfl⟩, hne⟩ := rp_mem_roundParts.1 hp
      exact ⟨hne, fun f hf => (rp_mem_redPart.1 hf).1⟩
    · exact ⟨(hQa p hp).1, (hQa p hp).2.trans hblueE⟩
  · intro p hp p' hp' hpp'
    simp only [Finset.coe_union, Set.mem_union, Finset.mem_coe] at hp hp'
    -- generic disjointness via elements
    have key : ∀ p ∈ roundParts E col, ∀ p' ∈ roundParts E col ∪ Q, p ≠ p' →
        Disjoint p p' := by
      intro p hp p' hp' hpp'
      obtain ⟨⟨x, hx, rfl⟩, _⟩ := rp_mem_roundParts.1 hp
      rw [Finset.disjoint_left]
      intro f hf hf'
      have hxf := (rp_mem_redPart.1 hf).2.1
      rcases Finset.mem_union.1 hp' with hp' | hp'
      · obtain ⟨⟨x', hx', rfl⟩, _⟩ := rp_mem_roundParts.1 hp'
        exact hpp' (by rw [rp_red_eq hx hxf hf' hx'])
      · have := (rp_mem_blue.1 ((hQa p' hp').2 hf')).2 x hxf
        simp_all
    rcases hp with hp | hp
    · exact key p hp p' (by simp_all) hpp'
    rcases hp' with hp' | hp'
    · exact (key p' hp' p (by simp_all) (Ne.symm hpp')).symm
    · exact hQb hp hp' hpp'
  · intro S ⟨hS1, hS2⟩
    set S2 := S.filter (fun e => ∃ q ∈ Q, e ∈ q) with hS2def
    have hS2ind : IsPartIndep Q S2 := by
      refine ⟨fun e he => (Finset.mem_filter.1 he).2, fun q hq => ?_⟩
      refine le_trans (Finset.card_le_card ?_) (hS2 q (Finset.mem_union_right _ hq))
      exact Finset.inter_subset_inter_right (Finset.filter_subset _ _)
    have hS2ac := hQc S2 hS2ind
    intro u c hc
    by_cases hall : ∀ e ∈ c.edges, e ∈ (SimpleGraph.fromEdgeSet (S2 : Set (Sym2 V))).edgeSet
    · exact hS2ac _ (hc.transfer hall)
    push_neg at hall
    obtain ⟨e, hec, heS2⟩ := hall
    have heS : e ∈ (SimpleGraph.fromEdgeSet (S : Set (Sym2 V))).edgeSet := c.edges_subset_edgeSet hec
    rw [SimpleGraph.edgeSet_fromEdgeSet] at heS
    have heS' : e ∈ S := heS.1
    have heS2' : e ∉ S2 := by
      intro h; apply heS2; rw [SimpleGraph.edgeSet_fromEdgeSet]; exact ⟨h, heS.2⟩
    obtain ⟨p, hp, hep⟩ := hS1 e heS'
    have hpR : p ∈ roundParts E col := by
      rcases Finset.mem_union.1 hp with hp | hp
      · exact hp
      · exact absurd (Finset.mem_filter.2 ⟨heS', p, hp, hep⟩) heS2'
    obtain ⟨⟨x, hx, rfl⟩, hpne⟩ := rp_mem_roundParts.1 hpR
    have hxe : x ∈ e := (rp_mem_redPart.1 hep).2.1
    -- every S-edge containing x lies in redPart x
    have hinc : ∀ f ∈ S, x ∈ f → f ∈ redPart E col x := by
      intro f hfS hxf
      obtain ⟨p', hp', hfp'⟩ := hS1 f hfS
      rcases Finset.mem_union.1 hp' with hp' | hp'
      · obtain ⟨⟨x', hx', rfl⟩, _⟩ := rp_mem_roundParts.1 hp'
        exact rp_in_redPart_of hx hxf hfp' hx'
      · have := (rp_mem_blue.1 ((hQa p' hp').2 hfp')).2 x hxf
        simp_all
    have hcard := hS2 _ hp
    -- rotate cycle to start at x
    have hxs : x ∈ c.support := by
      induction e using Sym2.ind with
      | h a b =>
        rcases Sym2.mem_iff.1 hxe with rfl | rfl
        · exact c.fst_mem_support_of_mem_edges hec
        · exact c.snd_mem_support_of_mem_edges hec
    have hc' := hc.rotate hxs
    generalize c.rotate x hxs = d at hc'
    cases d with
    | nil => exact hc'.not_of_nil
    | cons h p =>
      rename_i y
      rw [SimpleGraph.Walk.cons_isCycle_iff] at hc'
      obtain ⟨hpath, hnot⟩ := hc'
      -- last edge of p contains x
      have hyx : y ≠ x := (h.ne).symm
      obtain ⟨f, hfp, hxf⟩ : ∃ f ∈ p.edges, x ∈ f := by
        cases hr : p.reverse with
        | nil => exact absurd rfl hyx
        | cons h' q =>
          rename_i z
          refine ⟨s(x, z), ?_, Sym2.mem_mk_left _ _⟩
          have : s(x, z) ∈ p.reverse.edges := by rw [hr]; simp
          simpa using this
      have hfS : f ∈ S := by
        have := p.edges_subset_edgeSet hfp
        rw [SimpleGraph.edgeSet_fromEdgeSet] at this
        exact this.1
      have h0S : s(x, y) ∈ S := by
        have := h
        rw [SimpleGraph.fromEdgeSet_adj] at this
        exact this.1
      have hfne : f ≠ s(x, y) := fun h => hnot (h ▸ hfp)
      apply hfne
      have h1 : f ∈ S ∩ redPart E col x := Finset.mem_inter.2 ⟨hfS, hinc f hfS hxf⟩
      have h2 : s(x, y) ∈ S ∩ redPart E col x :=
        Finset.mem_inter.2 ⟨h0S, hinc _ h0S (Sym2.mem_mk_left _ _)⟩
      exact Finset.card_le_one.1 hcard _ h1 _ h2

lemma rp_main : ∀ (n : ℕ) (E : Finset (Sym2 V)), E.card = n →
    ∀ P ∈ (partitionPMF E).support, RPInv E P := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro E hE P hP
  rw [partitionPMF] at hP
  split_ifs at hP with h
  · simp only [PMF.mem_support_bind_iff, PMF.support_map, Set.mem_image] at hP
    obtain ⟨e, _, b, _, c, _, Q, hQ, rfl⟩ := hP
    apply rp_step
    exact ih _ (hE ▸ blueEdges_card_lt E e b c) _ rfl Q hQ
  · rw [PMF.support_pure, Set.mem_singleton_iff] at hP
    subst hP
    refine ⟨⟨by simp, by simp⟩, fun S hS => ?_⟩
    have : S = ∅ := by
      ext e; simp only [Finset.notMem_empty, iff_false]
      intro he; obtain ⟨p, hp, _⟩ := hS.1 e he; simp at hp
    subst this; exact isAcyclicSet_empty

theorem random_partition_indep_acyclic_core {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    ∀ P ∈ (partitionPMF G.edgeFinset).support,
      IsPartitionOf G.edgeFinset P ∧
        ∀ S : Finset (Sym2 V), IsPartIndep P S → IsAcyclicSet S :=
  rp_main _ _ rfl

end SecretaryWD.Graphic

open SecretaryWD.Graphic


theorem solution {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    ∀ P ∈ (partitionPMF G.edgeFinset).support,
      IsPartitionOf G.edgeFinset P ∧
        ∀ S : Finset (Sym2 V), IsPartIndep P S → IsAcyclicSet S := by
  exact random_partition_indep_acyclic_core G
