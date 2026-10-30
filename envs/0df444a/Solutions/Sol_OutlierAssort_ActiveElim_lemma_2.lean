-- Prove2me | solution 1 for OutlierAssort.ActiveElim.lemma_2
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-29T17:07:39.995666+00:00
-- url     : https://prove2.me/submissions/c7fddc34-1523-4193-8b98-568f90889173

import Mathlib
import Definitions.Def_ChoiceCDLP_MNL_mnlObjective
import Definitions.Def_OutlierAssort_ActiveElim_Model

open OutlierAssort.ActiveElim

theorem solution {N : ℕ} (r v vhat : Fin N → ℝ) (hr : ∀ i, r i ∈ Set.Icc (0 : ℝ) 1)
    (hv : ∀ i, v i ∈ Set.Icc (0 : ℝ) 1) (hvhat : ∀ i, 0 ≤ vhat i) (S : Finset (Fin N)) :
    |rev r vhat S - rev r v S| ≤ 2 * (∑ i ∈ S, |vhat i - v i|) / (1 + ∑ i ∈ S, v i) := by
  unfold rev ChoiceCDLP.MNL.mnlObjective
  set a := ∑ j ∈ S, r j * vhat j with ha
  set b := ∑ j ∈ S, r j * v j with hb
  set W := ∑ j ∈ S, vhat j with hW
  set V := ∑ j ∈ S, v j with hV
  set D := ∑ i ∈ S, |vhat i - v i| with hD
  have hV0 : 0 ≤ V := Finset.sum_nonneg (fun i _ => (hv i).1)
  have hW0 : 0 ≤ W := Finset.sum_nonneg (fun i _ => hvhat i)
  have ha0 : 0 ≤ a := Finset.sum_nonneg (fun i _ => mul_nonneg (hr i).1 (hvhat i))
  have haW : a ≤ W := Finset.sum_le_sum (fun i _ => by
    have := (hr i).2; have := hvhat i; nlinarith)
  have hab : |a - b| ≤ D := by
    rw [ha, hb, ← Finset.sum_sub_distrib]
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum (fun i _ => ?_))
    rw [← mul_sub, abs_mul, abs_of_nonneg (hr i).1]
    have := (hr i).2
    have := abs_nonneg (vhat i - v i)
    nlinarith
  have hWV : |W - V| ≤ D := by
    rw [hW, hV, ← Finset.sum_sub_distrib]
    exact Finset.abs_sum_le_sum_abs _ _
  set R := a / (W + 1) with hR
  have hR0 : 0 ≤ R := div_nonneg ha0 (by linarith)
  have hR1 : R ≤ 1 := (div_le_one (by linarith)).2 (by linarith)
  have hRW : R * (W + 1) = a := div_mul_cancel₀ a (by linarith)
  have hpos : 0 < V + 1 := by linarith
  have key : R - b / (V + 1) = ((a - b) - R * (W - V)) / (V + 1) := by
    field_simp
    linarith
  rw [key, abs_div, abs_of_pos hpos, add_comm 1 V]
  apply div_le_div_of_nonneg_right _ hpos.le
  have h1 : |(a - b) - R * (W - V)| ≤ |a - b| + |R * (W - V)| := abs_sub _ _
  have h2 : |R * (W - V)| ≤ |W - V| := by
    rw [abs_mul, abs_of_nonneg hR0]
    have := abs_nonneg (W - V)
    nlinarith
  linarith
