-- Prove2me | solution 1 for OutcomeRebate.Transfer.assumption_2_equilibrium
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-21T20:41:10.872427+00:00
-- url     : https://prove2.me/submissions/bef26645-915b-467c-8863-ce7975845b3b

import Mathlib
import Definitions.Def_OutcomeRebate_Transfer_Model
import Theorems.Thm_OutcomeRebate_Transfer_theorem_1_part_1
import Theorems.Thm_OutcomeRebate_Transfer_theorem_2_part_1
import Theorems.Thm_OutcomeRebate_Transfer_zq_monotone

namespace OutcomeRebate.Transfer
open MeasureTheory

lemma obp_q0_bounds (α lam : ℝ) (hα : 0 < α ∧ α < 1) (hlam : 1 ≤ lam) :
    0 < q0 α lam ∧ q0 α lam < 1 := by
  have hL : 0 < lam ^ (-(1 / (1 - α))) := Real.rpow_pos_of_pos (by linarith) _
  unfold q0
  constructor
  · positivity
  · rw [div_lt_one (by linarith)]; linarith

theorem obp_assumption_2_equilibrium (P : Params) (hS : P.Standing) (hA1 : Assumption1 P) (q1 : ℝ)
    (hq1 : 0 < q1 ∧ q1 < 1 ∧ zOf P.α P.lam q1 * q1 = 2 / P.β) (hA2 : Assumption2 P q1) :
    (IsEqPriceU P (pStar P) ∧ coversU P (pStar P) ∧ ∀ p : ℝ, IsEqPriceU P p → p = pStar P) ∧
      (IsEqPriceO P (pTilde P) ∧ coversO P (pTilde P) ∧
        ∀ p : ℝ, IsEqPriceO P p → p = pTilde P) := by
  have hS' := hS
  obtain ⟨hn, hv, hc, hβ, hβh, hq0, hqlt, hα0, hα1, hlam, hvp⟩ := hS'
  have hM := zq_monotone P.α P.lam ⟨hα0, hα1⟩ hlam
  have hk : (1:ℝ) < 1 / P.β := by rw [lt_div_iff₀ hβ]; linarith
  have hmem : 1 / P.β ∈ (fun q => zOf P.α P.lam q * q) '' Set.Ioo 0 (q0 P.α P.lam) := by
    rw [hM.2.1]; exact hk
  obtain ⟨qb, ⟨hqb0, hqbq0⟩, hqb⟩ := hmem
  have hq0lt := (obp_q0_bounds P.α P.lam ⟨hα0, hα1⟩ hlam).2
  have hqbar1 : 0 < qb ∧ qb < 1 ∧ zOf P.α P.lam qb * qb = 1 / P.β :=
    ⟨hqb0, by linarith, hqb⟩
  have key : ∀ q : ℝ, 0 < q → q < 1 → (1 / P.β ≤ zOf P.α P.lam q * q ↔ q ≤ qb) :=
    hM.2.2.2 (1 / P.β) qb hk hqb0 (by linarith) hqb
  have h : P.q ≤ qb ∨
      (qb < P.q ∧ pStar P * (1 / P.q - P.z * P.β / 2) - P.vbar / 2 ≤ P.vp) := by
    rcases hA2.2 with h | h
    · left
      have : q1 ≤ qb := by
        rw [← key q1 hq1.1 hq1.2.1, hq1.2.2]
        exact div_le_div_of_nonneg_right (by norm_num) hβ.le
      linarith
    · by_cases hq : P.q ≤ qb
      · exact Or.inl hq
      · exact Or.inr ⟨lt_of_not_ge hq, h⟩
  exact ⟨theorem_1_part_1 P hS hA1 qb hqbar1 h, theorem_2_part_1 P hS hA1 hA2.1⟩


end OutcomeRebate.Transfer

open OutcomeRebate.Transfer

theorem solution (P : Params) (hS : P.Standing) (hA1 : Assumption1 P) (q1 : ℝ)
    (hq1 : 0 < q1 ∧ q1 < 1 ∧ zOf P.α P.lam q1 * q1 = 2 / P.β) (hA2 : Assumption2 P q1) :
    (IsEqPriceU P (pStar P) ∧ coversU P (pStar P) ∧ ∀ p : ℝ, IsEqPriceU P p → p = pStar P) ∧
      (IsEqPriceO P (pTilde P) ∧ coversO P (pTilde P) ∧
        ∀ p : ℝ, IsEqPriceO P p → p = pTilde P) :=
  obp_assumption_2_equilibrium P hS hA1 q1 hq1 hA2
