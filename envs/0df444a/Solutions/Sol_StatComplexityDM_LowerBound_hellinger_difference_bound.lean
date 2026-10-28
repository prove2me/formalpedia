-- Prove2me | solution 1 for StatComplexityDM.LowerBound.hellinger_difference_bound
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T14:45:18.667302+00:00
-- url     : https://prove2.me/submissions/0a82a630-94f0-4b60-9fea-6b263ef7c788

import Mathlib
import Definitions.Def_StatComplexityDM_LowerBound_Core
import Definitions.Def_FoundationsRL_GeneralDM_Divergences

open FoundationsRL.GeneralDM

namespace Aux_SCDM_hell

lemma pt (p x y ε : ℝ) (hp : 0 ≤ p)
    (h : p ≠ 0 → 0 ≤ x ∧ 0 ≤ y ∧ |x - y| ≤ ε) :
    p * (x - y) ^ 2 ≤ ε * (p * (x + y)) := by
  by_cases hp0 : p = 0
  · rw [hp0]; simp
  · obtain ⟨hx, hy, hz⟩ := h hp0
    have habs : |x - y| ≤ x + y := abs_le.mpr ⟨by linarith, by linarith⟩
    have hε : 0 ≤ ε := (abs_nonneg _).trans hz
    have h1 : (x - y) ^ 2 ≤ ε * (x + y) := by
      rw [← sq_abs]
      nlinarith [abs_nonneg (x - y)]
    nlinarith [mul_le_mul_of_nonneg_left h1 hp]

end Aux_SCDM_hell

open StatComplexityDM.LowerBound FoundationsRL.GeneralDM in
theorem solution {Ω : Type*} [Fintype Ω]
    (P Q : Ω → ℝ) (hP : IsDist P) (hQ : IsDist Q)
    (X Y : Ω → ℝ) (ε : ℝ)
    (hXP : ∀ ω, P ω ≠ 0 → 0 ≤ X ω ∧ 0 ≤ Y ω ∧ |X ω - Y ω| ≤ ε)
    (hXQ : ∀ ω, Q ω ≠ 0 → 0 ≤ X ω ∧ 0 ≤ Y ω ∧ |X ω - Y ω| ≤ ε) :
    |(∑ ω, P ω * (X ω - Y ω)) - (∑ ω, Q ω * (X ω - Y ω))| ≤
      Real.sqrt (8 * ε *
        ((∑ ω, P ω * (X ω + Y ω)) + (∑ ω, Q ω * (X ω + Y ω))) *
        hellingerSq P Q) := by
  have hdiff : (∑ ω, P ω * (X ω - Y ω)) - (∑ ω, Q ω * (X ω - Y ω)) =
      ∑ ω, (Real.sqrt (P ω) - Real.sqrt (Q ω)) *
        ((Real.sqrt (P ω) + Real.sqrt (Q ω)) * (X ω - Y ω)) := by
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro ω _
    have h1 := Real.sq_sqrt (hP.1 ω)
    have h2 := Real.sq_sqrt (hQ.1 ω)
    linear_combination (-(X ω - Y ω)) * h1 + (X ω - Y ω) * h2
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
    (fun ω => Real.sqrt (P ω) - Real.sqrt (Q ω))
    (fun ω => (Real.sqrt (P ω) + Real.sqrt (Q ω)) * (X ω - Y ω))
  have hterm : ∀ ω, ((Real.sqrt (P ω) + Real.sqrt (Q ω)) * (X ω - Y ω)) ^ 2 ≤
      2 * ε * (P ω * (X ω + Y ω) + Q ω * (X ω + Y ω)) := by
    intro ω
    have h1 := Real.sq_sqrt (hP.1 ω)
    have h2 := Real.sq_sqrt (hQ.1 ω)
    have hp := Aux_SCDM_hell.pt (P ω) (X ω) (Y ω) ε (hP.1 ω) (hXP ω)
    have hq := Aux_SCDM_hell.pt (Q ω) (X ω) (Y ω) ε (hQ.1 ω) (hXQ ω)
    have hk : ((Real.sqrt (P ω) + Real.sqrt (Q ω)) * (X ω - Y ω)) ^ 2 ≤
        2 * (P ω * (X ω - Y ω) ^ 2 + Q ω * (X ω - Y ω) ^ 2) := by
      nlinarith [mul_nonneg (sq_nonneg (Real.sqrt (P ω) - Real.sqrt (Q ω)))
        (sq_nonneg (X ω - Y ω))]
    nlinarith
  have hsumg : ∑ ω, ((Real.sqrt (P ω) + Real.sqrt (Q ω)) * (X ω - Y ω)) ^ 2 ≤
      2 * ε * ((∑ ω, P ω * (X ω + Y ω)) + (∑ ω, Q ω * (X ω + Y ω))) := by
    rw [← Finset.sum_add_distrib, Finset.mul_sum]
    exact Finset.sum_le_sum (fun ω _ => hterm ω)
  have hH : hellingerSq P Q = ∑ ω, (Real.sqrt (P ω) - Real.sqrt (Q ω)) ^ 2 := rfl
  have hHnn : 0 ≤ hellingerSq P Q := Finset.sum_nonneg (fun ω _ => sq_nonneg _)
  rw [hdiff]
  apply Real.abs_le_sqrt
  set S := (∑ ω, P ω * (X ω + Y ω)) + (∑ ω, Q ω * (X ω + Y ω))
  set L := ∑ ω, (Real.sqrt (P ω) - Real.sqrt (Q ω)) *
        ((Real.sqrt (P ω) + Real.sqrt (Q ω)) * (X ω - Y ω))
  have h1 : L ^ 2 ≤ hellingerSq P Q * (2 * ε * S) := by
    rw [hH]
    exact hcs.trans (mul_le_mul_of_nonneg_left hsumg (Finset.sum_nonneg (fun ω _ => sq_nonneg _)))
  have h2 : 0 ≤ hellingerSq P Q * (2 * ε * S) := (sq_nonneg L).trans h1
  nlinarith
