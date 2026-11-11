-- Prove2me | solution 1 for avram_bv_finite_times_eventually_separated
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-10T08:09:15.857469+00:00
-- url     : https://prove2.me/submissions/8c25ba0f-2530-4013-83b6-6414f3f296e1

import Mathlib

/- A sufficiently fine grid separates every pair of distinct times in a finite set. -/
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

theorem solution
    (s : Finset ℝ) (mesh : ℕ → ℝ)
    (hmesh : Filter.Tendsto mesh Filter.atTop (nhds (0 : ℝ))) :
    ∀ᶠ n in Filter.atTop, ∀ a ∈ s, ∀ b ∈ s,
      a ≠ b → mesh n < |a - b| := by
  classical
  have hpair (a b : ℝ) (hab : a ≠ b) :
      ∀ᶠ n in Filter.atTop, mesh n < |a - b| := by
    have hdist : (0 : ℝ) < |a - b| := abs_pos.mpr (sub_ne_zero.mpr hab)
    have hnhds : Set.Iio |a - b| ∈ nhds (0 : ℝ) :=
      isOpen_Iio.mem_nhds hdist
    exact hmesh.eventually hnhds
  have hcross (a : ℝ) (t : Finset ℝ) :
      ∀ᶠ n in Filter.atTop, ∀ b ∈ t, a ≠ b → mesh n < |a - b| := by
    induction t using Finset.induction with
    | empty =>
        filter_upwards [] with n b hb hab
        simp at hb
    | @insert b t hnot ih =>
        by_cases hab : a = b
        · filter_upwards [ih] with n ht c hc hac
          rcases Finset.mem_insert.mp hc with hcb | hct
          · exact (hac (hab.trans hcb.symm)).elim
          · exact ht c hct hac
        · filter_upwards [ih, hpair a b hab] with n ht hpairn c hc hac
          rcases Finset.mem_insert.mp hc with hcb | hct
          · subst c
            exact hpairn
          · exact ht c hct hac
  induction s using Finset.induction with
  | empty =>
      filter_upwards [] with n a ha b hb hab
      simp at ha
  | @insert a t hat ih =>
      filter_upwards [ih, hcross a t] with n ht hc p hp q hq hpq
      rcases Finset.mem_insert.mp hp with hpa | hpt
      · subst p
        rcases Finset.mem_insert.mp hq with hqa | hqt
        · subst q
          exact (hpq rfl).elim
        · exact hc q hqt hpq
      · rcases Finset.mem_insert.mp hq with hqa | hqt
        · subst q
          rw [abs_sub_comm]
          exact hc p hpt hpq.symm
        · exact ht p hpt q hqt hpq
