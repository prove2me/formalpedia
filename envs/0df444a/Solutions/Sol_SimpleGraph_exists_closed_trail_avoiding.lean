-- Prove2me | solution 1 for SimpleGraph.exists_closed_trail_avoiding
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T17:54:05.500126+00:00
-- url     : https://prove2.me/submissions/67cc52d8-d2f1-453f-9198-938d024378c8

module
public import Definitions.Def_Euler_Basic
public import Definitions.Def_Euler_Trail
public import Theorems.Thm_SimpleGraph_exists_adj_not_mem_of_countP_ne

set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph
open Walk
variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]
namespace SimpleGraph
theorem _root_.solution {S : List (Sym2 V)} (hS : S.Nodup)
    (hSsub : ∀ e ∈ S, e ∈ G.edgeSet)
    (hpar : ∀ y, Even (S.countP fun e => y ∈ e) ↔ Even (G.degree y))
    {x y₀ : V} (hxy : G.Adj x y₀) (hnot : s(x, y₀) ∉ S) :
    ∃ c : G.Walk x x, c.IsTrail ∧ 0 < c.length ∧ ∀ e ∈ c.edges, e ∉ S := by
  by_contra hno
  have key : ∀ k : ℕ, ∃ v, ∃ q : G.Walk x v,
      q.IsTrail ∧ 0 < q.length ∧ (∀ e ∈ q.edges, e ∉ S) ∧ k ≤ q.length := by
    intro k
    induction k with
    | zero => exact ⟨y₀, cons hxy nil, by simp, by simp, by simpa using hnot, by simp⟩
    | succ k ih =>
      obtain ⟨v, q, hq, hpos, hdisj, hk⟩ := ih
      by_cases hv : v = x
      · subst hv
        exact absurd ⟨q, hq, hpos, hdisj⟩ hno
      have hqodd : ¬ Even (q.edges.countP fun e => v ∈ e) := by
        rw [hq.even_countP_edges_iff]
        simp [Ne.symm hv]
      have hnd : (S ++ q.edges).Nodup :=
        List.nodup_append.mpr ⟨hS, hq.edges_nodup, fun a ha b hb hab => hdisj b hb (hab ▸ ha)⟩
      have hsub : ∀ e ∈ S ++ q.edges, e ∈ G.edgeSet := by
        intro e he
        rcases List.mem_append.mp he with he | he
        · exact hSsub e he
        · exact q.edges_subset_edgeSet he
      have hne : (S ++ q.edges).countP (fun e => v ∈ e) ≠ G.degree v := by
        intro heq
        have := hpar v
        rw [← heq, List.countP_append, Nat.even_add] at this
        tauto
      obtain ⟨w, hvw, hw⟩ := exists_adj_not_mem_of_countP_ne hnd hsub hne
      rw [List.mem_append, not_or] at hw
      refine ⟨w, (cons hvw.symm q.reverse).reverse, ?_, ?_, ?_, ?_⟩
      · refine ((isTrail_cons _ _).mpr ⟨hq.reverse, ?_⟩).reverse
        rw [edges_reverse, List.mem_reverse, Sym2.eq_swap]
        exact hw.2
      · simp
      · intro e he
        simp only [edges_reverse, edges_cons, List.reverse_cons, List.reverse_reverse,
          List.mem_append, List.mem_singleton] at he
        rcases he with he | rfl
        · exact hdisj e he
        · rw [Sym2.eq_swap]
          exact hw.1
      · simp
        omega
  obtain ⟨v, q, hq, -, -, hk⟩ := key (G.edgeFinset.card + 1)
  have := hq.length_le_card_edgeFinset
  omega
end SimpleGraph
