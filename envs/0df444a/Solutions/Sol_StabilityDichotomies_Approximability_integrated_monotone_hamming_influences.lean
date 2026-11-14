-- Prove2me | solution 1 for StabilityDichotomies.Approximability.integrated_monotone_hamming_influences
-- status  : ACCEPTED   (prove)
-- author  : @wcysai
-- created : 2026-11-13T07:26:45.120228+00:00
-- url     : https://prove2.me/submissions/3eb4f790-bda6-4818-98e1-2d8b11ad71d7

import Theorems.Thm_StabilityDichotomies_Approximability_integrated_monotone_bernoulli_influences
import Theorems.Thm_StabilityDichotomies_Approximability_monotone_hamming_height
noncomputable section
open scoped Classical BigOperators Interval
open MeasureTheory StabilityDichotomies.Approximability

theorem solution {ι V : Type} [Fintype ι] [Fintype V]
    (out : (ι → Bool) → V → Bool) (hmono : Monotone out) (B ε : ℝ)
    (hbound : ∀ x, (∑ v : V, if out x v then (1 : ℝ) else 0) ≤ B)
    (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) :
    (∫ p in (1-ε)..1, p * ∑ i : ι, ∑ x : ι → Bool,
      (∏ j : ι, if x j then p else 1-p) *
      (hammingDist (out (Function.update x i true)) (out (Function.update x i false)) : ℝ)) ≤ B := by
  let H : (ι → Bool) → ℝ := fun x => ∑ v : V, if out x v then 1 else 0
  have hH : Monotone H := by
    intro a b hab
    apply Finset.sum_le_sum
    intro v hv
    have hv := hmono hab v
    cases ha : out a v <;> cases hb : out b v <;> simp_all
    exact False.elim ((by decide : ¬ ((true : Bool) ≤ false)) hv)
  have hrange (x : ι → Bool) : 0 ≤ H x ∧ H x ≤ B := by
    constructor
    · apply Finset.sum_nonneg
      intro v hv
      split_ifs <;> norm_num
    · exact hbound x
  have hdist (i : ι) (x : ι → Bool) :
      (hammingDist (out (Function.update x i true)) (out (Function.update x i false)) : ℝ) =
      H (Function.update x i true) - H (Function.update x i false) := by
    have hmask : Function.update x i false ≤ Function.update x i true := by
      intro j
      by_cases hj : j = i
      · subst j; simp
      · simp [Function.update,hj]
    rw [hammingDist_comm]
    exact monotone_hamming_height _ _ (hmono hmask)
  have hint := integrated_monotone_bernoulli_influences H B ε hH hrange hε0 hε1
  simp_rw [hdist]
  exact hint
