-- Prove2me | solution 1 for SupplyChainTheory.shang_song_bounds
-- status  : ACCEPTED   (disprove)
-- author  : @Nickrobbins95
-- created : 2026-09-30T17:11:19.994662+00:00
-- url     : https://prove2.me/submissions/00c5cb4d-2f96-4579-958f-226d37088fc8

import Mathlib
import Definitions.Def_SupplyChainTheory_multiechelon

/-! Disproof of `SupplyChainTheory.shang_song_bounds`.
Counterexample: N = 2, h = 1, p = 1, D 1 = dirac (-1), D j = dirac 0 otherwise,
S* = -1 everywhere, j = 2, y = -1: csG = -1 but ssUpper = -2. -/

open MeasureTheory SupplyChainTheory in
noncomputable def cxD_84057eee : ℕ → Measure ℝ :=
  fun j => if j = 1 then Measure.dirac (-1) else Measure.dirac 0

open MeasureTheory SupplyChainTheory in
instance cxInst_84057eee (j : ℕ) : IsProbabilityMeasure (cxD_84057eee j) := by
  unfold cxD_84057eee; split_ifs <;> infer_instance

open MeasureTheory SupplyChainTheory in
theorem cxD1_84057eee : cxD_84057eee 1 = Measure.dirac (-1) := by simp [cxD_84057eee]

open MeasureTheory SupplyChainTheory in
theorem cxD2_84057eee : cxD_84057eee 2 = Measure.dirac 0 := by simp [cxD_84057eee]

open MeasureTheory SupplyChainTheory in
theorem lh1_84057eee : localHolding 2 (fun _ => (1:ℝ)) 1 = 2 := by
  simp [localHolding]

open MeasureTheory SupplyChainTheory in
theorem lh3_84057eee : localHolding 2 (fun _ => (1:ℝ)) 3 = 0 := by
  simp [localHolding]

open MeasureTheory SupplyChainTheory in
theorem g1_84057eee (y : ℝ) : csG 2 (fun _ => 1) 1 cxD_84057eee (fun _ => -1) 1 y
    = (y + 1) + 3 * max (-(y+1)) 0 := by
  simp only [csG, csHat, cxD1_84057eee, integral_dirac]
  simp [csBar, lh1_84057eee]; norm_num

open MeasureTheory SupplyChainTheory in
theorem g2_84057eee (y : ℝ) : csG 2 (fun _ => 1) 1 cxD_84057eee (fun _ => -1) 2 y
    = y + ((min (-1) y + 1) + 3 * max (-(min (-1) y + 1)) 0) := by
  simp only [csG, csHat, cxD2_84057eee, integral_dirac]
  simp only [csBar, lh1_84057eee]
  rw [show (0:ℕ)+1 = 1 from rfl, cxD1_84057eee, integral_dirac]
  ring_nf

open MeasureTheory SupplyChainTheory in
theorem seq_84057eee : CSSequential 2 (fun _ => 1) 1 cxD_84057eee (fun _ => -1) := by
  intro j hj y
  simp only [Finset.mem_Icc] at hj
  obtain ⟨h1, h2⟩ := hj
  interval_cases j
  · rw [g1_84057eee, g1_84057eee]; norm_num
    rcases le_total 0 (y+1) with h | h
    · rw [max_eq_right (by linarith)]; linarith
    · rw [max_eq_left (by linarith)]; linarith
  · rw [g2_84057eee, g2_84057eee]; norm_num
    rcases le_total (-1) y with h | h
    · rw [min_eq_left h]; norm_num; linarith
    · rw [min_eq_right h]; norm_num; linarith

open MeasureTheory SupplyChainTheory in
theorem upper_val_84057eee : ssUpper 2 (fun _ => 1) 1 cxD_84057eee 2 (-1) = -2 := by
  simp only [ssUpper, nvCostOf, pipelineMean, lh3_84057eee]
  have ht : tildeLaw cxD_84057eee 2 = Measure.dirac (-1) := by
    simp only [tildeLaw]
    rw [cxD1_84057eee, cxD2_84057eee, Measure.dirac_conv_dirac, Measure.dirac_conv_dirac]; norm_num
  rw [ht, integral_dirac]
  simp [cxD1_84057eee, lh3_84057eee]

open MeasureTheory SupplyChainTheory in
theorem integrable_84057eee (j : ℕ) : Integrable (fun x : ℝ => x) (cxD_84057eee j) := by
  unfold cxD_84057eee; split_ifs <;> exact integrable_dirac (by simp)

open SupplyChainTheory in
theorem solution : ¬ (∀ (N : ℕ) (h : ℕ → ℝ) (p : ℝ) (D : ℕ → MeasureTheory.Measure ℝ)
    [∀ j, MeasureTheory.IsProbabilityMeasure (D j)]
    (hD : ∀ j, MeasureTheory.Integrable (fun x => x) (D j))
    (hh : ∀ j, 0 < h j) (hp : 0 < p) (Sstar : ℕ → ℝ) (hS : CSSequential N h p D Sstar)
    (j : ℕ) (hj1 : 1 ≤ j) (hjN : j ≤ N),
    (∀ y, ssLower N h p D j y ≤ csG N h p D Sstar j y
        ∧ csG N h p D Sstar j y ≤ ssUpper N h p D j y)
      ∧ ∃ Sl Su : ℝ, IsMinOn (ssUpper N h p D j) Set.univ Sl
          ∧ IsMinOn (ssLower N h p D j) Set.univ Su ∧ Sl ≤ Sstar j ∧ Sstar j ≤ Su) := by
  intro H
  have key := ((H 2 (fun _ => 1) 1 cxD_84057eee integrable_84057eee (fun _ => one_pos) one_pos
    (fun _ => -1) seq_84057eee 2 (by norm_num) le_rfl).1 (-1)).2
  rw [g2_84057eee, upper_val_84057eee] at key
  norm_num at key
