-- Prove2me | solution 1 for avram_chat24_uniform_step_pointwise_core
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-13T09:29:30.6962+00:00
-- url     : https://prove2.me/submissions/42db1531-ceee-4dad-a9c0-602b7fae28f5

import Mathlib
import Theorems.Thm_avram_chat24_uniform_left_cell_limit_core
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter
open scoped NNReal ENNReal Topology
noncomputable section
theorem solution
    (F Y : ℝ≥0 → ℝ) (a b : ℝ) (B : ℝ≥0) (hB : 0 < B)
    (hband : ∀ s, s ≤ B → F s ∈ Icc a b)
    (hpre : ∀ t, 0 < t → t ≤ B →
      Y t ∈ Icc a b ∧ Tendsto F (𝓝[<] t) (nhds (Y t)))
    (w : ℝ → ℝ) (hw : ContinuousOn w (Icc a b))
    (k : ℝ≥0 → ℝ) (L M : ℝ) (hL : 0 ≤ L)
    (hkb : ∀ t, ‖k t‖ ≤ L) (hM : ∀ y ∈ Icc a b, ‖w y‖ ≤ M) :
    let u : ℕ → ℕ → ℝ≥0 := fun n i => B * (i : ℝ≥0) / ((n + 1 : ℕ) : ℝ≥0)
    let G : ℕ → ℝ≥0 → ℝ := fun n =>
      ∑ i ∈ Finset.range (n + 1), (Ioc (u n i) (u n (i + 1))).indicator
        (fun t => k t * w (F (u n i)))
    ∀ t : ℝ≥0, 0 < t → t ≤ B →
      (∀ n, ‖G n t‖ ≤ L * M) ∧
      Tendsto (fun n => G n t) atTop (nhds (k t * w (Y t))) := by
  classical
  intro u G t ht htB
  obtain ⟨κ, hc, huniq, htend⟩ := avram_chat24_uniform_left_cell_limit_core B hB t ht htB
  have heq (n : ℕ) : G n t = k t * w (F (u n (κ n))) := by
    have hcell : u n (κ n) < t ∧ t ≤ u n (κ n + 1) := ⟨(hc n).2.1, (hc n).2.2⟩
    simp only [G, Finset.sum_apply, Set.indicator_apply, mem_Ioc]
    rw [Finset.sum_eq_single (κ n)]
    · simp only [if_pos hcell]
    · intro j hj hne
      have hn : ¬ (u n j < t ∧ t ≤ u n (j + 1)) := by
        intro hh
        exact hne (huniq n j hh.1 hh.2)
      simp only [if_neg hn]
    · intro hnot
      exact False.elim (hnot (Finset.mem_range.mpr (hc n).1))
  have hF : Tendsto (fun n => F (u n (κ n))) atTop (nhds (Y t)) :=
    (hpre t ht htB).2.comp htend
  have hFwithin : Tendsto (fun n => F (u n (κ n))) atTop (𝓝[Icc a b] (Y t)) :=
    tendsto_nhdsWithin_iff.mpr ⟨hF, Filter.Eventually.of_forall
      (fun n => hband _ ((hc n).2.1.le.trans htB))⟩
  refine ⟨?_, ?_⟩
  · intro n
    rw [heq, norm_mul]
    exact mul_le_mul (hkb t) (hM _ (hband _ ((hc n).2.1.le.trans htB)))
      (norm_nonneg _) hL
  · simpa only [heq, Function.comp_def] using tendsto_const_nhds.mul
      ((hw (Y t) (hpre t ht htB).1).tendsto.comp hFwithin)
end
