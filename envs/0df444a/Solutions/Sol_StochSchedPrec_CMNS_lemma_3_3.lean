-- Prove2me | solution 1 for StochSchedPrec.CMNS.lemma_3_3
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-05T17:27:31.513742+00:00
-- url     : https://prove2.me/submissions/e88dfd46-22fd-416b-ae22-67bc659c8541

import Mathlib
import Definitions.Def_StochSchedPrec_CMNS_Model
import Definitions.Def_StochSchedPrec_CMNS_Algorithm

open MeasureTheory ProbabilityTheory

open StochSchedPrec.CMNS in
theorem solution {V : Type*} [Fintype V] [DecidableEq V]
    (m : ℕ) (hm : 0 < m) (Δ : ℝ) (hΔ : 0 ≤ Δ) (μ : V → ℝ) (hμ : ∀ j, 0 ≤ μ j)
    (C : V → ℝ) (hload : ∀ W : Finset V, loadFn m Δ μ W ≤ ∑ j ∈ W, μ j * C j)
    (hlow : ∀ j, μ j ≤ C j)
    (L : Fin (Fintype.card V) ≃ V) (hL : IsSortedBy L C) (j : V) :
    1 / (m : ℝ) * ∑ i ∈ before L j, μ i ≤ (1 + max 1 (((m : ℝ) - 1) / m * Δ)) * C j := by
  set W := before L j
  set S := ∑ i ∈ W, μ i with hSdef
  set Q := ∑ i ∈ W, μ i ^ 2 with hQdef
  set x := C j
  set M := max 1 (((m : ℝ) - 1) / m * Δ) with hM
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hCle : ∀ i ∈ W, C i ≤ x := by
    intro i hi
    have hi' : L.symm i ≤ L.symm j := (Finset.mem_filter.mp hi).2
    have := hL _ _ hi'
    simpa using this
  have hx : 0 ≤ x := le_trans (hμ j) (hlow j)
  have hS : 0 ≤ S := Finset.sum_nonneg (fun i _ => hμ i)
  have hQ : 0 ≤ Q := Finset.sum_nonneg (fun i _ => sq_nonneg (μ i))
  have hSC : ∑ i ∈ W, μ i * C i ≤ S * x := by
    rw [hSdef, Finset.sum_mul]
    exact Finset.sum_le_sum (fun i hi => mul_le_mul_of_nonneg_left (hCle i hi) (hμ i))
  have hQS : Q ≤ S * x := by
    rw [hQdef, hSdef, Finset.sum_mul]
    refine Finset.sum_le_sum (fun i hi => ?_)
    rw [sq]
    exact mul_le_mul_of_nonneg_left (le_trans (hlow i) (hCle i hi)) (hμ i)
  have hW := hload W
  unfold loadFn at hW
  rw [← hSdef, ← hQdef] at hW
  have key : S ^ 2 + Q - ((m : ℝ) - 1) * (Δ - 1) * Q ≤ 2 * m * (S * x) := by
    have h2 : 1 / (2 * (m : ℝ)) * (S ^ 2 + Q) - ((m : ℝ) - 1) * (Δ - 1) / (2 * (m : ℝ)) * Q
        = (S ^ 2 + Q - ((m : ℝ) - 1) * (Δ - 1) * Q) / (2 * m) := by
      field_simp
    rw [h2, div_le_iff₀ (by positivity)] at hW
    have := mul_le_mul_of_nonneg_right hSC (by positivity : (0:ℝ) ≤ 2 * m)
    linarith
  -- bound S ≤ c * x
  have hM1 : (1 : ℝ) ≤ M := le_max_left _ _
  have hM2 : ((m : ℝ) - 1) / m * Δ ≤ M := le_max_right _ _
  have hc : S ^ 2 ≤ (m * (1 + M)) * (S * x) := by
    set k := ((m : ℝ) - 1) * (Δ - 1)
    rcases le_or_gt k 1 with hk | hk
    · have : 0 ≤ (1 - k) * Q := mul_nonneg (by linarith) hQ
      have h1 : S ^ 2 ≤ 2 * m * (S * x) := by nlinarith
      have h3 : 2 * (m : ℝ) ≤ m * (1 + M) := by nlinarith
      have h4 : 0 ≤ S * x := mul_nonneg hS hx
      nlinarith
    · have h1 : (1 - k) * (S * x) ≤ (1 - k) * Q :=
        mul_le_mul_of_nonpos_left hQS (by linarith)
      have h2 : S ^ 2 ≤ (2 * m - 1 + k) * (S * x) := by nlinarith
      have h3 : 2 * (m : ℝ) - 1 + k = m * (1 + ((m : ℝ) - 1) / m * Δ) := by
        simp only [k]
        field_simp
        ring
      have h5 : m * (1 + ((m : ℝ) - 1) / m * Δ) ≤ m * (1 + M) :=
        mul_le_mul_of_nonneg_left (by linarith) hmR.le
      have h4 : 0 ≤ S * x := mul_nonneg hS hx
      rw [h3] at h2
      nlinarith
  have hS' : S ≤ (m * (1 + M)) * x := by
    rcases eq_or_lt_of_le hS with h0 | hpos
    · rw [← h0]
      have : 0 ≤ (1 + M) := by linarith
      positivity
    · have : S * S ≤ S * ((m * (1 + M)) * x) := by nlinarith
      exact le_of_mul_le_mul_left this hpos
  rw [div_mul_eq_mul_div, one_mul, div_le_iff₀ hmR]
  nlinarith
