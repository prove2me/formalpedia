-- Prove2me | solution 1 for TenChallenges.minor_of_topologicalMinor
-- status  : ACCEPTED   (prove)
-- author  : @Davide
-- created : 2026-11-18T12:40:52.382034+00:00
-- url     : https://prove2.me/submissions/92c050e7-b3a3-4bc9-bccf-e2b7cec7c1b5

import Mathlib
import Definitions.Def_TenChallenges_Minor
import Definitions.Def_TenChallenges_TopologicalMinor

open SimpleGraph

namespace TenChallenges.TopMinor

variable {W V : Type} {H : SimpleGraph W} {G : SimpleGraph V}

/-- The interior part of the path of `ab` assigned to `a`: the reversed path with its first
vertex (the branch vertex of `b`) removed. It runs from the second vertex to `φ a`. -/
noncomputable def piece (T : TopologicalMinor H G) {a b : W} (h : H.Adj a b) :=
  (T.path h).reverse.tail

theorem not_nil_rev (T : TopologicalMinor H G) {a b : W} (h : H.Adj a b) :
    ¬ (T.path h).reverse.Nil :=
  Walk.not_nil_of_ne (fun e => H.ne_of_adj h (T.vertexMap.injective e).symm)

theorem piece_support (T : TopologicalMinor H G) {a b : W} (h : H.Adj a b) :
    (piece T h).support = ((T.path h).support.reverse).tail := by
  unfold piece
  rw [Walk.support_tail_of_not_nil _ (not_nil_rev T h), Walk.support_reverse]

theorem mem_path_of_mem_piece (T : TopologicalMinor H G) {a b : W} (h : H.Adj a b) {v : V}
    (hv : v ∈ (piece T h).support) : v ∈ (T.path h).support := by
  rw [piece_support] at hv
  exact List.mem_reverse.mp (List.mem_of_mem_tail hv)

theorem ne_of_mem_piece (T : TopologicalMinor H G) {a b : W} (h : H.Adj a b) {v : V}
    (hv : v ∈ (piece T h).support) : v ≠ T.vertexMap b := by
  rintro rfl
  have hnd : ((T.path h).reverse.support).Nodup :=
    (Walk.isPath_def _).mp (T.path_isPath h).reverse
  rw [Walk.support_eq_cons] at hnd
  have hv' : T.vertexMap b ∈ (T.path h).reverse.support.tail := by
    have := piece_support T h
    rw [← Walk.support_reverse] at this
    rw [← this]; exact hv
  exact (List.nodup_cons.mp hnd).1 hv'

theorem end_mem_piece (T : TopologicalMinor H G) {a b : W} (h : H.Adj a b) :
    T.vertexMap a ∈ (piece T h).support :=
  Walk.end_mem_support _

end TenChallenges.TopMinor

open TenChallenges.TopMinor in
theorem solution {W V : Type} {H : SimpleGraph W} {G : SimpleGraph V}
    (T : SimpleGraph.TopologicalMinor H G) : Nonempty (SimpleGraph.Minor H G) := by
  classical
  letI : LinearOrder W := linearOrderOfSTO WellOrderingRel
  let φ := T.vertexMap
  -- branch set of `a`: its branch vertex and the pieces of the paths to larger neighbours
  let B : W → Set V := fun a =>
    {φ a} ∪ {v | ∃ b, a < b ∧ ∃ h : H.Adj a b, v ∈ (piece T h).support}
  refine ⟨{ branchSet := B, pairwise_disjoint_branchSet := ?_,
            connectedOn_branchSet := ?_, exists_mem_branchSet_of_adj := ?_ }⟩
  · -- disjointness
    intro a c hac
    rw [Set.disjoint_left]
    rintro v hva hvc
    -- a vertex of a piece of `ab` that is a branch vertex `φ x` must be `φ a`
    have key : ∀ {a b : W} (h : H.Adj a b) (x : W), φ x ∈ (piece T h).support → x = a := by
      intro a b h x hx
      rcases T.path_branch h x (mem_path_of_mem_piece T h hx) with rfl | rfl
      · rfl
      · exact absurd rfl (ne_of_mem_piece T h hx)
    rcases hva with hva | ⟨b, hab, h, hvb⟩ <;> rcases hvc with hvc | ⟨d, hcd, k, hvd⟩
    · exact hac (φ.injective ((Set.mem_singleton_iff.mp hva).symm.trans
        (Set.mem_singleton_iff.mp hvc)))
    · rw [Set.mem_singleton_iff.mp hva] at hvd
      exact hac (key k a hvd)
    · rw [Set.mem_singleton_iff.mp hvc] at hvb
      exact hac (key h c hvb).symm
    · have hne : s(a, b) ≠ s(c, d) := by
        intro e
        rcases Sym2.eq_iff.mp e with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact hac rfl
        · exact lt_asymm hab hcd
      obtain ⟨x, rfl⟩ := T.path_disjoint h k hne v (mem_path_of_mem_piece T h hvb)
        (mem_path_of_mem_piece T k hvd)
      exact hac ((key h x hvb).symm.trans (key k x hvd))
  · -- connectivity
    intro a
    apply G.induce_connected_of_patches (φ a) (Or.inl rfl)
    rintro v (hv | ⟨b, hab, h, hv⟩)
    · rw [Set.mem_singleton_iff.mp hv]
      exact ⟨{φ a}, Set.subset_union_left, rfl, rfl, Reachable.refl _⟩
    · refine ⟨{x | x ∈ (piece T h).support}, ?_, end_mem_piece T h, hv, ?_⟩
      · intro x hx; exact Or.inr ⟨b, hab, h, hx⟩
      · exact (Walk.connected_induce_support (piece T h)) _ _
  · -- adjacency
    have adj_lt : ∀ {a b : W} (hab : a < b) (h : H.Adj a b),
        ∃ v₁ ∈ B a, ∃ v₂ ∈ B b, G.Adj v₁ v₂ := by
      intro a b hab h
      refine ⟨(T.path h).reverse.snd, Or.inr ⟨b, hab, h, ?_⟩, φ b, Or.inl rfl,
        (Walk.adj_snd (not_nil_rev T h)).symm⟩
      exact Walk.start_mem_support _
    intro a b h
    rcases lt_trichotomy a b with hab | rfl | hba
    · exact adj_lt hab h
    · exact absurd h (H.loopless.irrefl a)
    · obtain ⟨v₁, h₁, v₂, h₂, hv⟩ := adj_lt hba h.symm
      exact ⟨v₂, h₂, v₁, h₁, hv.symm⟩
