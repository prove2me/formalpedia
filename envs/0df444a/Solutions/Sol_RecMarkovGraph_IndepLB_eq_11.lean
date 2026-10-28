-- Prove2me | solution 1 for RecMarkovGraph.IndepLB.eq_11
-- status  : ACCEPTED   (prove)
-- author  : @frknbls
-- created : 2026-10-27T15:02:48.217434+00:00
-- url     : https://prove2.me/submissions/045d1469-0820-4be0-88ce-76bd7f49636b

import Definitions.Def_RecMarkovGraph_IndepLB_Model

namespace RecMarkovGraph.IndepLB
open Finset

/-- Caro–Wei, relative to a vertex subset `s`: some independent `I ⊆ s` has
`∑_{v ∈ s} 1/(deg_s v + 1) ≤ |I|`. -/
theorem caroWei_aux' {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
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

theorem lemma_5_1_aux {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] :
    max (((Fintype.card V : ℝ)) ^ 2 / ((Fintype.card V : ℝ) + 2 * (G.edgeFinset.card : ℝ)))
        ((2 * (Fintype.card V : ℝ) - (G.edgeFinset.card : ℝ)) / 3) ≤ (G.indepNum : ℝ) := by
  obtain ⟨I, -, hI, hsum⟩ := caroWei_aux' G _ (univ : Finset V) rfl
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

theorem recSeq_mem (a x : ℝ) (ha : 0 ≤ a) (ha1 : a ≤ 1) (hx : 0 ≤ x) (hx1 : x ≤ 1) :
    ∀ k, 0 ≤ recSeq a x k ∧ recSeq a x k ≤ 1 := by
  intro k
  induction k with
  | zero => exact ⟨hx, hx1⟩
  | succ k ih =>
    obtain ⟨h0, h1⟩ := ih
    simp only [recSeq, fa]
    have h2 : a * recSeq a x k ≤ 1 := by nlinarith
    have h3 : 0 ≤ a * recSeq a x k := mul_nonneg ha h0
    constructor
    · exact mul_nonneg h0 (by linarith)
    · nlinarith

theorem rmrgWeight_nonneg (n : ℕ) (p r : ℝ) (hp : 0 < p) (hp1 : p ≤ 1) (hr : 0 < r)
    (hr1 : r < 1) (G : SimpleGraph (Fin n)) : 0 ≤ rmrgWeight n p r G := by
  unfold rmrgWeight
  apply Finset.prod_nonneg
  intro i _
  unfold chainWeight
  split_ifs
  · norm_num
  all_goals
    apply mul_nonneg
    · linarith
    · apply Finset.prod_nonneg
      intro j _
      obtain ⟨hq0, hq1⟩ := recSeq_mem (1 - r) p (by linarith) (by linarith) hp.le hp1 j
      have : r * recSeq (1 - r) p j ≤ 1 := by nlinarith
      unfold stepWeight
      split_ifs <;> nlinarith

theorem rmrgProb_mono (n : ℕ) (p r : ℝ) (hp : 0 < p) (hp1 : p ≤ 1) (hr : 0 < r)
    (hr1 : r < 1) (E F : SimpleGraph (Fin n) → Prop) (hEF : ∀ G, E G → F G) :
    rmrgProb n p r E ≤ rmrgProb n p r F := by
  unfold rmrgProb
  apply Finset.sum_le_sum
  intro G _
  apply mul_le_mul_of_nonneg_left _ (rmrgWeight_nonneg n p r hp hp1 hr hr1 G)
  by_cases hE : E G
  · simp [hE, hEF G hE]
  · simp only [hE, if_false]; split_ifs <;> norm_num

theorem eq_11 (p r : ℝ) (hp : 0 < p) (hp1 : p ≤ 1) (hr : 0 < r) (hr1 : r < 1)
    (ε ε₀ : ℝ) (hε₀ : 0 < ε₀) (hε₀ε : ε₀ < ε) (n : ℕ)
    (hn : Real.exp ((1 - r) / (ε - ε₀)) < (n : ℝ)) :
    rmrgProb n p r (fun G =>
        (n : ℝ) / ((2 + ε₀) / (1 - r) * Real.log n + 1) ≤ (G.indepNum : ℝ)) ≤
      rmrgProb n p r (fun G =>
        (n : ℝ) / ((2 + ε) / (1 - r) * Real.log n) ≤ (G.indepNum : ℝ)) ∧
    rmrgProb n p r (fun G => avgDeg G / Real.log n ≤ (2 + ε₀) / (1 - r)) ≤
      rmrgProb n p r (fun G =>
        (n : ℝ) / ((2 + ε₀) / (1 - r) * Real.log n + 1) ≤ (G.indepNum : ℝ)) := by
  have hnpos : (0 : ℝ) < n := lt_trans (Real.exp_pos _) hn
  have hdε : 0 < ε - ε₀ := by linarith
  have h1r : 0 < 1 - r := by linarith
  have hL : (1 - r) / (ε - ε₀) < Real.log n := (Real.lt_log_iff_exp_lt hnpos).mpr hn
  have hLpos : 0 < Real.log n := lt_trans (by positivity) hL
  set L := Real.log n with hLdef
  have hD1 : 0 < (2 + ε₀) / (1 - r) * L + 1 := by positivity
  have hD12 : (2 + ε₀) / (1 - r) * L + 1 ≤ (2 + ε) / (1 - r) * L := by
    have : 1 < (ε - ε₀) * L / (1 - r) := by
      rw [lt_div_iff₀ h1r]
      rw [div_lt_iff₀ hdε] at hL
      linarith
    have e : (2 + ε) / (1 - r) * L = (2 + ε₀) / (1 - r) * L + (ε - ε₀) * L / (1 - r) := by
      field_simp; ring
    linarith
  constructor
  · apply rmrgProb_mono n p r hp hp1 hr hr1
    intro G hG
    exact le_trans (div_le_div_of_nonneg_left hnpos.le hD1 hD12) hG
  · apply rmrgProb_mono n p r hp hp1 hr hr1
    intro G hG
    classical
    have h51 := lemma_5_1_aux G
    have hmax := le_trans (le_max_left _ _) h51
    simp only [Fintype.card_fin] at hmax
    have hdeg : avgDeg G ≤ (2 + ε₀) / (1 - r) * L := by
      rw [div_le_iff₀ hLpos] at hG; linarith
    unfold avgDeg at hdeg
    have hE0 : (0 : ℝ) ≤ G.edgeFinset.card := Nat.cast_nonneg _
    have hkey : (n : ℝ) ^ 2 / ((n : ℝ) + 2 * G.edgeFinset.card) =
        (n : ℝ) / (2 * G.edgeFinset.card / n + 1) := by
      field_simp
      ring
    have hpos2 : 0 < 2 * (G.edgeFinset.card : ℝ) / n + 1 := by positivity
    calc (n : ℝ) / ((2 + ε₀) / (1 - r) * L + 1)
        ≤ (n : ℝ) / (2 * G.edgeFinset.card / n + 1) :=
          div_le_div_of_nonneg_left hnpos.le hpos2 (by linarith)
      _ = (n : ℝ) ^ 2 / ((n : ℝ) + 2 * G.edgeFinset.card) := hkey.symm
      _ ≤ G.indepNum := by convert hmax using 3

end RecMarkovGraph.IndepLB


-- Platform entry point: restates the target verbatim.
namespace RecMarkovGraph.IndepLB

theorem _root_.solution (p r : ℝ) (hp : 0 < p) (hp1 : p ≤ 1) (hr : 0 < r) (hr1 : r < 1)
    (ε ε₀ : ℝ) (hε₀ : 0 < ε₀) (hε₀ε : ε₀ < ε) (n : ℕ)
    (hn : Real.exp ((1 - r) / (ε - ε₀)) < (n : ℝ)) :
    rmrgProb n p r (fun G =>
        (n : ℝ) / ((2 + ε₀) / (1 - r) * Real.log n + 1) ≤ (G.indepNum : ℝ)) ≤
      rmrgProb n p r (fun G =>
        (n : ℝ) / ((2 + ε) / (1 - r) * Real.log n) ≤ (G.indepNum : ℝ)) ∧
    rmrgProb n p r (fun G => avgDeg G / Real.log n ≤ (2 + ε₀) / (1 - r)) ≤
      rmrgProb n p r (fun G =>
        (n : ℝ) / ((2 + ε₀) / (1 - r) * Real.log n + 1) ≤ (G.indepNum : ℝ)) := by
  apply @RecMarkovGraph.IndepLB.eq_11 <;> assumption

end RecMarkovGraph.IndepLB
