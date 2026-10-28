-- Prove2me | solution 1 for RobustSAA.Univariate.ks_le_kuiper
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T02:22:45.812174+00:00
-- url     : https://prove2.me/submissions/12bfb15d-edb7-4401-9896-7d9ecfcaa556

import Mathlib
import Definitions.Def_RobustSAA_Univariate_Setting

open Filter MeasureTheory

open RobustSAA.Univariate in
theorem solution {N : ℕ} (hN : 0 < N) (F₀ : ProbabilityMeasure ℝ) (s : Fin N → ℝ) :
    ksStat F₀ s ≤ kuiperStat F₀ s := by
  have hu0 : ∀ i, 0 ≤ u F₀ s i := fun i => by
    unfold u cdfOf; exact ProbabilityTheory.cdf_nonneg _ _
  have hu1 : ∀ i, u F₀ s i ≤ 1 := fun i => by
    unfold u cdfOf; exact ProbabilityTheory.cdf_le_one _ _
  haveI : Nonempty (Fin N) := ⟨⟨0, hN⟩⟩
  unfold ksStat kuiperStat
  set A := ⨆ i : Fin N, (((i : ℕ) + 1 : ℝ) / N - u F₀ s i) with hAdef
  set B := ⨆ i : Fin N, (u F₀ s i - ((i : ℕ) : ℝ) / N) with hBdef
  have hA : ∀ i : Fin N, ((i : ℕ) + 1 : ℝ) / N - u F₀ s i ≤ A := fun i => by
    rw [hAdef]
    exact le_ciSup (f := fun i : Fin N => ((i : ℕ) + 1 : ℝ) / N - u F₀ s i)
      (Finite.bddAbove_range _) i
  have hB : ∀ i : Fin N, u F₀ s i - ((i : ℕ) : ℝ) / N ≤ B := fun i => by
    rw [hBdef]
    exact le_ciSup (f := fun i : Fin N => u F₀ s i - ((i : ℕ) : ℝ) / N)
      (Finite.bddAbove_range _) i
  have hB0 : 0 ≤ B := by
    have h := hB ⟨0, hN⟩
    simp only [Nat.cast_zero, zero_div, sub_zero] at h
    exact (hu0 _).trans h
  have hA0 : 0 ≤ A := by
    have h := hA ⟨N - 1, by omega⟩
    have hc : (((N - 1 : ℕ) : ℝ) + 1) / N = 1 := by
      rw [Nat.cast_sub (by omega), Nat.cast_one, sub_add_cancel,
        div_self (by exact_mod_cast hN.ne')]
    simp only at h
    rw [hc] at h
    linarith [hu1 ⟨N - 1, by omega⟩]
  apply ciSup_le
  intro i
  apply max_le
  · linarith [hA i]
  · linarith [hB i]
