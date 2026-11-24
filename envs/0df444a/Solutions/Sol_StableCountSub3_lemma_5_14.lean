-- Prove2me | solution 1 for StableCountSub3.lemma_5_14
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @CGTMoyano
-- created : 2026-11-24T18:37:10.604716+00:00
-- url     : https://prove2.me/submissions/26526c5d-b1b6-49a1-b679-12e75aa968d9
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_StableCountSub3_Credits
import Theorems.Thm_StableCountSub3_theorem_2_10
import Theorems.Thm_StableCountSub3_lemma_3_8
import Theorems.Thm_StableCountSub3_lemma_5_8
import Theorems.Thm_StableCountSub3_lemma_5_13

open StableMatching

noncomputable section

namespace StableCountSub3.L514

open Classical

variable {n : ℕ}

theorem mem_stableSet (I : Instance n) (μ : Matching n) : μ ∈ stableSet I ↔ I.IsStable μ := by
  unfold stableSet; simp

theorem card_stableSet (I : Instance n) : (stableSet I).card = StableCount.numStable I := by
  unfold StableCount.numStable
  rw [Fintype.card_subtype]
  rfl

theorem stableSet_nonempty (I : Instance n) : (stableSet I).Nonempty := by
  obtain ⟨-, -, -, h4, -, -⟩ := theorem_2_10 I
  have hD : IsDownset I (∅ : Finset (Rot n)) := ⟨Finset.empty_subset _, fun ρ hρ => absurd hρ (by simp)⟩
  exact ⟨muOf I ∅, (mem_stableSet I _).mpr (h4 ∅ hD).1⟩

theorem three_le (x : ℕ∞) (h : (3 : ℕ∞) ≤ x) : x = 3 ∨ 4 ≤ x := by
  rcases eq_or_lt_of_le h with h | h
  · exact Or.inl h.symm
  · right
    have := Order.add_one_le_of_lt h
    exact le_trans (by norm_num) this

theorem not_four_le_three : ¬ (4 : ℕ∞) ≤ 3 := by
  intro h
  have : ((4 : ℕ) : ℕ∞) ≤ ((3 : ℕ) : ℕ∞) := by exact_mod_cast h
  exact absurd (ENat.natCast_le_natCast.mp this) (by decide)

/-- By Lemma 3.8 the simple men are exactly `B ∪ C`, a disjoint union. -/
theorem card_B_add_card_C (I : Instance n) (D : Finset (Rot n)) (hD : IsDownset I D) (dir : Dir) :
    ((Finset.univ.filter fun m => InB I D m dir).card : ℝ) +
        ((Finset.univ.filter fun m => InC I D m dir).card : ℝ) =
      ∑ m, if IsSimple I D m dir then (1 : ℝ) else 0 := by
  rw [Finset.sum_boole]
  have hunion : (Finset.univ.filter fun m => IsSimple I D m dir) =
      (Finset.univ.filter fun m => InB I D m dir) ∪ (Finset.univ.filter fun m => InC I D m dir) := by
    ext m
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union]
    constructor
    · intro hS
      have h3 := lemma_3_8 I D hD m dir 2 (by norm_num)
      rcases three_le _ (by exact_mod_cast h3) with h | h
      · exact Or.inr ⟨hS, h⟩
      · exact Or.inl ⟨hS, h⟩
    · rintro (h | h)
      · exact h.1
      · exact h.1
  have hdisj : Disjoint (Finset.univ.filter fun m => InB I D m dir)
      (Finset.univ.filter fun m => InC I D m dir) := by
    rw [Finset.disjoint_filter]
    intro m _ hB hC
    have := hB.2
    rw [hC.2] at this
    exact not_four_le_three this
  rw [hunion, Finset.card_union_of_disjoint hdisj]
  push_cast
  ring

/-- The `i`-th term of `δ₁`. -/
def g (i : ℕ) : ℝ :=
  2 * Real.log (((i : ℝ) + 1 + 1) / ((i : ℝ) + 1)) /
    (((i : ℝ) + 1 + 1) * ((i : ℝ) + 1 + 2) * ((i : ℝ) + 1 + 3))

theorem g_nonneg (i : ℕ) : 0 ≤ g i := by
  unfold g
  apply div_nonneg
  · apply mul_nonneg (by norm_num)
    apply Real.log_nonneg
    rw [le_div_iff₀ (by positivity)]
    linarith
  · positivity

theorem g_le (i : ℕ) : g i ≤ 2 * (1 / ((i + 1 : ℕ) : ℝ) ^ 2) := by
  unfold g
  push_cast
  have hpos : (0 : ℝ) < (i : ℝ) + 1 := by positivity
  have hL : Real.log (((i : ℝ) + 1 + 1) / ((i : ℝ) + 1)) ≤ 1 := by
    have := Real.log_le_sub_one_of_pos (x := ((i : ℝ) + 1 + 1) / ((i : ℝ) + 1)) (by positivity)
    have h2 : ((i : ℝ) + 1 + 1) / ((i : ℝ) + 1) - 1 ≤ 1 := by
      rw [div_sub_one hpos.ne', div_le_one hpos]
      have : (0 : ℝ) ≤ i := by positivity
      linarith
    linarith
  have hP : ((i : ℝ) + 1) ^ 2 ≤ ((i : ℝ) + 1 + 1) * ((i : ℝ) + 1 + 2) * ((i : ℝ) + 1 + 3) := by
    have : (0 : ℝ) ≤ i := by positivity
    nlinarith
  calc 2 * Real.log (((i : ℝ) + 1 + 1) / ((i : ℝ) + 1)) /
        (((i : ℝ) + 1 + 1) * ((i : ℝ) + 1 + 2) * ((i : ℝ) + 1 + 3))
      ≤ 2 * 1 / (((i : ℝ) + 1 + 1) * ((i : ℝ) + 1 + 2) * ((i : ℝ) + 1 + 3)) := by
        apply div_le_div_of_nonneg_right _ (by positivity)
        linarith
    _ ≤ 2 * 1 / ((i : ℝ) + 1) ^ 2 := by
        apply div_le_div_of_nonneg_left (by norm_num) (by positivity) hP
    _ = 2 * (1 / ((i : ℝ) + 1) ^ 2) := by ring

theorem g_summable : Summable g := by
  have hs : Summable (fun i : ℕ => 1 / ((i + 1 : ℕ) : ℝ) ^ 2) :=
    (summable_nat_add_iff 1).mpr (Real.summable_one_div_nat_pow.mpr one_lt_two)
  exact Summable.of_nonneg_of_le g_nonneg g_le (hs.mul_left 2)

theorem delta_one_sub_delta_two : delta 1 - delta 2 = 2 * Real.log 2 / (2 * 3 * 4) := by
  have h1 : delta 1 = ∑' i, g i := by
    unfold delta g
    congr 1
    funext i
    push_cast
    ring_nf
  have h2 : delta 2 = ∑' i, g (i + 1) := by
    unfold delta g
    congr 1
    funext i
    push_cast
    ring_nf
  rw [h1, h2, g_summable.tsum_eq_zero_add]
  unfold g
  norm_num

theorem delta_one_sub_delta_two_pos : 0 < delta 1 - delta 2 := by
  rw [delta_one_sub_delta_two]
  have : 0 < Real.log 2 := Real.log_pos (by norm_num)
  positivity

end StableCountSub3.L514

end

open StableCountSub3 StableCountSub3.L514 in
open Classical in
theorem solution {n : ℕ} (hn : 1 ≤ n) (I : Instance n) :
    gBasic I = 2 * delta 1 - (delta 1 - delta 2) * es I ∧
    2 / 3 * (delta 1 + 2 * delta 2) ≤ gBasic I := by
  obtain ⟨h1, -, -, -, -, -⟩ := theorem_2_10 I
  set N : ℝ := (StableCount.numStable I : ℝ) with hN
  set k : ℝ := delta 1 - delta 2 with hk
  set T : Matching n → ℝ := fun μ => ∑ m : Fin n,
    ((if IsSimple I (Dof I μ) m .bwd then (1 : ℝ) else 0) +
      (if IsSimple I (Dof I μ) m .fwd then (1 : ℝ) else 0)) with hT
  have hNpos : 0 < N := by
    rw [hN, ← card_stableSet]
    exact_mod_cast (stableSet_nonempty I).card_pos
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  have hes : es I = 1 / (N * n) * ∑ μ ∈ stableSet I, T μ := rfl
  have hg : gBasic I = 1 / (N * n) * ∑ μ ∈ stableSet I, (2 * n * delta 1 - k * T μ) := by
    unfold gBasic avgDm
    congr 1
    apply Finset.sum_congr rfl
    intro μ hμ
    have hD : IsDownset I (Dof I μ) := (h1 μ ((mem_stableSet I μ).mp hμ)).2.2
    rw [Finset.sum_add_distrib, lemma_5_8 I _ hD .fwd, lemma_5_8 I _ hD .bwd,
      card_B_add_card_C I _ hD .fwd, card_B_add_card_C I _ hD .bwd]
    simp only [hT, Finset.sum_add_distrib]
    ring
  have hgeq : gBasic I = 2 * delta 1 - k * es I := by
    rw [hg, hes, Finset.sum_sub_distrib, Finset.sum_const, card_stableSet, nsmul_eq_mul,
      ← Finset.mul_sum]
    field_simp
    ring
  refine ⟨hgeq, ?_⟩
  have hkpos : 0 < k := delta_one_sub_delta_two_pos
  have hes43 : es I ≤ 4 / 3 := (lemma_5_13 I).2.2
  rw [hgeq]
  nlinarith
