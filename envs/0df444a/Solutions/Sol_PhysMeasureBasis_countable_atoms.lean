-- Prove2me | solution 1 for PhysMeasureBasis.countable_atoms
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-10T18:59:57.050996+00:00
-- url     : https://prove2.me/submissions/63f9aaa1-6b9c-4e2d-a00a-7be80750478d

-- Generated from PhysMeasureBasis.lean — solution of PhysMeasureBasis.countable_atoms
import Mathlib
import Definitions.Def_PhysMeasureBasis
import Definitions.Def_ChapterA4
open PhysMeasureBasis



open MeasureTheory Set ProbabilityTheory
open scoped ENNReal

noncomputable section

set_option maxHeartbeats 1000000 in
theorem solution {α : Type*} [MeasurableSpace α]
    [MeasurableSingletonClass α] (μ : Measure α) [IsFiniteMeasure μ] :
    {x | μ {x} ≠ 0}.Countable := by

  by_contra! h;
  -- Since μ is finite, there exists some ε > 0 such that the set {x | μ {x} > ε} is uncountable.
  obtain ⟨ε, hε_pos, hε_uncountable⟩ : ∃ ε > 0, ¬Set.Countable {x : α | μ {x} > ε} := by
    by_cases hε : ∀ ε > 0, Set.Countable {x : α | μ {x} > ε};
    · refine False.elim (h ?_)
      convert Set.countable_iUnion fun n : ℕ => hε (1 / (n + 1)) (by simp +decide) using 1
      ext x
      simp only [ne_eq, mem_setOf_eq, one_div, gt_iff_lt, mem_iUnion]
      constructor <;> intro hx
      · rcases ENNReal.exists_inv_nat_lt hx with ⟨ n, hn ⟩;
        exact ⟨ n, lt_of_le_of_lt ( by simp ) hn ⟩;
      · exact ne_of_gt ( lt_of_le_of_lt ( by positivity ) hx.choose_spec );
    · exact by push_neg at hε; exact hε;
  -- Since {x | μ {x} > ε} is uncountable, we can find an infinite subset of it.
  obtain ⟨s, hs_inf, hs_subset⟩ : ∃ s : Set α, s.Infinite ∧ s ⊆ {x : α | μ {x} > ε} := by
    exact ⟨ _, fun h => hε_uncountable <| h.countable, Set.Subset.refl _ ⟩;
  -- Since $s$ is infinite, we can find a finite subset $t$ of $s$ such that $\mu(t) > \mu(\alpha)$.
  obtain ⟨t, ht_finite, ht_subset⟩ : ∃ t : Finset α, t.card > μ Set.univ / ε ∧ ∀ x ∈ t, x ∈ s := by
    rcases ENNReal.lt_iff_exists_real_btwn.mp (show μ Set.univ / ε < ⊤ from
      ENNReal.div_lt_top (MeasureTheory.measure_ne_top _ _) hε_pos.ne') with ⟨r, hr⟩;
    rcases exists_nat_gt r with ⟨ n, hn ⟩;
    rcases hs_inf.exists_subset_card_eq n with ⟨ t, ht ⟩;
    exact ⟨t, lt_of_lt_of_le hr.2.1
      (le_trans (ENNReal.ofReal_le_ofReal hn.le) (by simp +decide [ht.2])), fun x hx => ht.1 hx⟩;
  -- Since $t$ is a finite subset of $s$, we have $\mu(t) \geq t.card \cdot \epsilon$.
  have ht_measure : μ (t : Set α) ≥ t.card * ε := by
    have ht_measure : μ (t : Set α) ≥ ∑ x ∈ t, μ {x} := by
      rw [ ← MeasureTheory.measure_biUnion_finset ];
      · exact MeasureTheory.measure_mono ( by aesop_cat );
      · exact fun x hx y hy hxy => Set.disjoint_singleton.2 hxy;
      · exact fun x hx => MeasurableSingletonClass.measurableSet_singleton x;
    exact le_trans (by simp +decide [mul_comm]) (ht_measure.trans'
      (Finset.sum_le_sum fun x hx => le_of_lt (hs_subset (ht_subset x hx))));
  rw [gt_iff_lt, ENNReal.div_lt_iff] at ht_finite <;>
    simp_all +decide only [ne_eq, gt_iff_lt, mul_comm, ge_iff_le,
      Measure.measure_univ_eq_zero, measure_ne_top, not_false_eq_true, or_true]
  · exact ht_finite.not_ge
      (ht_measure.trans (MeasureTheory.measure_mono (Set.subset_univ _)));
  · aesop
