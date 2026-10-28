-- Prove2me | solution 1 for RecMarkovGraph.IndepLB.lemma_5_1
-- status  : ACCEPTED   (prove)
-- author  : @frknbls
-- created : 2026-10-27T14:55:41.477044+00:00
-- url     : https://prove2.me/submissions/a3c8f346-332c-4627-9a5f-d06f051a46e9

import Definitions.Def_RecMarkovGraph_IndepLB_Model

namespace RecMarkovGraph.IndepLB

open Finset

/-- Caro–Wei, relative to a vertex subset `s`: some independent `I ⊆ s` has
`∑_{v ∈ s} 1/(deg_s v + 1) ≤ |I|`. -/
theorem caroWei_aux {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] :
    ∀ (k : ℕ) (s : Finset V), s.card = k →
      ∃ I : Finset V, I ⊆ s ∧ G.IsIndepSet (I : Set V) ∧
        ∑ v ∈ s, (1 : ℝ) / ((s.filter (G.Adj v)).card + 1) ≤ I.card := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
  intro s hs
  rcases s.eq_empty_or_nonempty with h | hne
  · subst h; exact ⟨∅, by simp, by simp, by simp⟩
  obtain ⟨v, hv, hmin⟩ := s.exists_min_image (fun u => (s.filter (G.Adj u)).card) hne
  set N := s.filter (G.Adj v) with hN
  set s' := s \ insert v N with hs'
  have hsub : insert v N ⊆ s := by
    intro x hx
    rcases mem_insert.mp hx with rfl | hx
    · exact hv
    · exact (mem_filter.mp hx).1
  have hcard : s'.card < k := by
    rw [← hs, hs', card_sdiff_of_subset hsub]
    have : 0 < (insert v N).card := card_pos.mpr ⟨v, mem_insert_self _ _⟩
    have : (insert v N).card ≤ s.card := card_le_card hsub
    omega
  obtain ⟨I', hI's, hI'ind, hI'sum⟩ := ih _ hcard s' rfl
  have hvI' : v ∉ I' := fun h => by
    have := hI's h
    rw [hs', mem_sdiff] at this
    exact this.2 (mem_insert_self _ _)
  refine ⟨insert v I', ?_, ?_, ?_⟩
  · intro x hx
    rcases mem_insert.mp hx with rfl | hx
    · exact hv
    · exact (mem_sdiff.mp (hI's hx)).1
  · rw [coe_insert, SimpleGraph.IsIndepSet, Set.pairwise_insert]
    refine ⟨hI'ind, fun b hb _ => ?_⟩
    have hb' := hI's hb
    rw [hs', mem_sdiff, mem_insert, not_or] at hb'
    have hnadj : ¬ G.Adj v b := fun h => hb'.2.2 (mem_filter.mpr ⟨hb'.1, h⟩)
    exact ⟨hnadj, fun h => hnadj h.symm⟩
  · have hvN : v ∉ N := fun h => G.irrefl (mem_filter.mp h).2
    rw [card_insert_of_notMem hvI', ← sum_sdiff hsub]
    push_cast
    have h1 : ∑ x ∈ insert v N, (1 : ℝ) / ((s.filter (G.Adj x)).card + 1) ≤ 1 := by
      calc ∑ x ∈ insert v N, (1 : ℝ) / ((s.filter (G.Adj x)).card + 1)
          ≤ ∑ x ∈ insert v N, (1 : ℝ) / (N.card + 1) := by
            apply sum_le_sum
            intro x hx
            apply one_div_le_one_div_of_le (by positivity)
            have := hmin x (hsub hx)
            exact_mod_cast Nat.add_le_add_right this 1
        _ = 1 := by
            rw [sum_const, card_insert_of_notMem hvN, nsmul_eq_mul]
            push_cast
            field_simp
    have h2 : ∑ x ∈ s \ insert v N, (1 : ℝ) / ((s.filter (G.Adj x)).card + 1) ≤
        ∑ x ∈ s', (1 : ℝ) / ((s'.filter (G.Adj x)).card + 1) := by
      apply sum_le_sum
      intro x hx
      apply one_div_le_one_div_of_le (by positivity)
      have : (s'.filter (G.Adj x)).card ≤ (s.filter (G.Adj x)).card :=
        card_le_card (filter_subset_filter _ sdiff_subset)
      exact_mod_cast Nat.add_le_add_right this 1
    linarith

theorem lemma_5_1 {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] :
    max (((Fintype.card V : ℝ)) ^ 2 / ((Fintype.card V : ℝ) + 2 * (G.edgeFinset.card : ℝ)))
        ((2 * (Fintype.card V : ℝ) - (G.edgeFinset.card : ℝ)) / 3) ≤ (G.indepNum : ℝ) := by
  obtain ⟨I, -, hI, hsum⟩ := caroWei_aux G _ (univ : Finset V) rfl
  have hdeg : ∀ v, (univ.filter (G.Adj v)).card = G.degree v := by
    intro v
    rw [← G.card_neighborFinset_eq_degree, G.neighborFinset_eq_filter]
  simp_rw [hdeg] at hsum
  have hα : (I.card : ℝ) ≤ G.indepNum := by exact_mod_cast hI.card_le_indepNum
  have hdsum : ∑ v, (G.degree v : ℝ) = 2 * (G.edgeFinset.card : ℝ) := by
    exact_mod_cast G.sum_degrees_eq_twice_card_edges
  apply max_le
  · have := sq_sum_div_le_sum_sq_div (univ : Finset V) (fun _ => (1 : ℝ))
      (g := fun v => (G.degree v : ℝ) + 1) (fun v _ => by positivity)
    simp only [sum_const, card_univ, nsmul_eq_mul, mul_one, one_pow] at this
    rw [sum_add_distrib, hdsum, sum_const, card_univ, nsmul_eq_mul, mul_one] at this
    have h3 : (Fintype.card V : ℝ) ^ 2 / ((Fintype.card V : ℝ) + 2 * G.edgeFinset.card) =
        (Fintype.card V : ℝ) ^ 2 / (2 * G.edgeFinset.card + Fintype.card V) := by
      rw [add_comm]
    rw [h3]
    linarith
  · have hpt : ∀ v, (4 - (G.degree v : ℝ)) / 6 ≤ 1 / ((G.degree v : ℝ) + 1) := by
      intro v
      rw [div_le_div_iff₀ (by norm_num) (by positivity)]
      rcases Nat.lt_or_ge (G.degree v) 2 with h | h
      · have : (G.degree v : ℝ) ≤ 1 := by exact_mod_cast Nat.lt_succ_iff.mp h
        have h0 : (0 : ℝ) ≤ G.degree v := by positivity
        nlinarith
      · have : (2 : ℝ) ≤ G.degree v := by exact_mod_cast h
        nlinarith
    have := sum_le_sum fun v (_ : v ∈ (univ : Finset V)) => hpt v
    rw [← sum_div, sum_sub_distrib, hdsum, sum_const, card_univ, nsmul_eq_mul] at this
    have h4 : (2 * (Fintype.card V : ℝ) - G.edgeFinset.card) / 3 =
        ((Fintype.card V : ℝ) * 4 - 2 * G.edgeFinset.card) / 6 := by ring
    rw [h4]
    linarith

end RecMarkovGraph.IndepLB


-- Platform entry point: restates the target verbatim.
namespace RecMarkovGraph.IndepLB

theorem _root_.solution {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] :
    max (((Fintype.card V : ℝ)) ^ 2 / ((Fintype.card V : ℝ) + 2 * (G.edgeFinset.card : ℝ)))
        ((2 * (Fintype.card V : ℝ) - (G.edgeFinset.card : ℝ)) / 3) ≤ (G.indepNum : ℝ) := by
  apply @RecMarkovGraph.IndepLB.lemma_5_1 <;> assumption

end RecMarkovGraph.IndepLB
