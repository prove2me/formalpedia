-- Prove2me | solution 1 for QuantileMDP.theorem_4_counterexample
-- status  : ACCEPTED   (prove)
-- author  : @shuffle
-- created : 2026-11-14T02:44:29.836169+00:00
-- url     : https://prove2.me/submissions/92a22195-de53-4e12-9854-dfdd3cce9280

import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Definitions.Def_QuantileMDP_quantile
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Definitions.Def_QuantileMDP_opt
import Definitions.Def_QuantileMDP_upperCVaR

open MeasureTheory
open scoped ENNReal

namespace QuantileMDP

/-- The valid mixture identity in Appendix B.2.4. All branches use the
same global threshold in the positive-part expectation. -/
theorem cvar_mixture_positive_part {ι : Type*} [Fintype ι]
    (p : ι → ℝ≥0∞) (hp : ∀ i, p i ≠ ∞) (ν : ι → Measure ℝ) (τ x : ℝ)
    (hx : x = (quantile (∑ i, p i • ν i) τ).toReal)
    (hν : ∀ i, Integrable (fun y : ℝ => max (y - x) 0) (ν i)) :
    upperCVaR (∑ i, p i • ν i) τ =
      x + (∑ i, (p i).toReal * ∫ y, max (y - x) 0 ∂ν i) / (1 - τ) := by
  unfold upperCVaR
  dsimp only
  rw [← hx, integral_finsetSum_measure (fun i _ => (hν i).smul_measure (hp i))]
  simp only [integral_smul_measure, smul_eq_mul]

end QuantileMDP

namespace QuantileMDP

/-- The upper-tail CVaR of a deterministic reward is that reward. -/
theorem upperCVaR_dirac (c τ : ℝ) (hτ : τ ∈ Set.Ioo (0 : ℝ) 1) :
    upperCVaR (Measure.dirac c) τ = c := by
  have hq : quantile (Measure.dirac c) τ = (c : EReal) := by
    rw [quantile, if_neg hτ.1.ne', if_neg hτ.2.ne]
    apply le_antisymm
    · refine sInf_le ⟨c, ?_, rfl⟩
      change ENNReal.ofReal τ ≤ Measure.dirac c (Set.Iic c)
      rw [Measure.dirac_apply_of_mem (Set.mem_Iic.mpr le_rfl)]
      exact ENNReal.ofReal_le_one.mpr hτ.2.le
    · apply le_sInf
      rintro _ ⟨x, hx, rfl⟩
      apply EReal.coe_le_coe_iff.mpr
      by_contra! h
      have hz : Measure.dirac c (Set.Iic x) = 0 := by
        rw [Measure.dirac_apply, Set.indicator_of_notMem (show c ∉ Set.Iic x from h.not_ge)]
      have hl : ENNReal.ofReal τ ≤ Measure.dirac c (Set.Iic x) := hx
      rw [hz] at hl
      exact (ENNReal.ofReal_pos.mpr hτ.1).not_ge hl
  simp [upperCVaR, hq, integral_dirac]

end QuantileMDP

open Set QuantileMDP

namespace QuantileMDP

/-- In the one-state, one-step model with reward one and quantile level one
half, zero is an optimal allocation in the corrected quantile problem.
The multiplier used in Theorem 4 would return two at that allocation. -/
theorem theorem_4_allocation_counterexample :
    let p : Unit → ℝ := fun _ => 1
    let g : Unit → ℝ → EReal := fun _ _ => 1
    let q : Unit → ℝ := fun _ => 0
    q ∈ Feasible p (1 / 2) ∧
      (⨅ i, ⨅ (_ : q i ≠ 1), g i (q i)) = opt p g (1 / 2) ∧
      (∑ i, p i * (1 - q i) * (1 : ℝ)) / (1 - 1 / 2) = 2 := by
  dsimp only
  have hq : (fun _ : Unit => (0 : ℝ)) ∈ Feasible (fun _ => 1) (1 / 2) := by
    exact ⟨fun _ => ⟨le_rfl, zero_le_one⟩, Or.inr (by simp)⟩
  refine ⟨hq, ?_, by norm_num⟩
  have hvalue (q : Unit → ℝ) (_ : q ∈ Feasible (fun _ => 1) (1 / 2)) :
      (⨅ i, ⨅ (_ : q i ≠ 1), (1 : EReal)) = 1 := by
    have hq1 : q () ≠ 1 := by
      intro h
      have hbudget := ‹q ∈ Feasible (fun _ => 1) (1 / 2)›.2
      simp only [one_mul, Fintype.sum_unique, h] at hbudget
      norm_num at hbudget
    apply le_antisymm (iInf_le_of_le () (iInf_le _ hq1))
    exact le_iInf fun _ => le_iInf fun _ => le_rfl
  rw [hvalue _ hq]
  exact le_antisymm (le_iSup_of_le _ (le_iSup_of_le hq (hvalue _ hq).ge))
    (iSup_le fun q => iSup_le fun h => (hvalue q h).le)

end QuantileMDP

namespace QuantileMDP

/-- For a deterministic reward of one, an optimal quantile allocation can
give the wrong upper-tail CVaR in the printed weighting formula. -/
theorem verified_theorem_4_counterexample :
    let p : Unit → ℝ := fun _ => 1
    let g : Unit → ℝ → EReal := fun _ _ => 1
    let q : Unit → ℝ := fun _ => 0
    q ∈ Feasible p (1 / 2) ∧
      (⨅ i, ⨅ (_ : q i ≠ 1), g i (q i)) = opt p g (1 / 2) ∧
      upperCVaR (MeasureTheory.Measure.dirac (1 : ℝ)) (1 / 2) <
        (∑ i, p i * (1 - q i) * (1 : ℝ)) / (1 - 1 / 2) := by
  obtain ⟨hf, hg, hval⟩ := theorem_4_allocation_counterexample
  refine ⟨hf, hg, ?_⟩
  rw [hval, upperCVaR_dirac 1 (1 / 2) (by norm_num [Set.mem_Ioo])]
  norm_num

end QuantileMDP

theorem solution :
    let p : Unit → ℝ := fun _ => 1
    let g : Unit → ℝ → EReal := fun _ _ => 1
    let q : Unit → ℝ := fun _ => 0
    q ∈ Feasible p (1 / 2) ∧
      (⨅ i, ⨅ (_ : q i ≠ 1), g i (q i)) = opt p g (1 / 2) ∧
      upperCVaR (MeasureTheory.Measure.dirac (1 : ℝ)) (1 / 2) <
        (∑ i, p i * (1 - q i) * (1 : ℝ)) / (1 - 1 / 2) := QuantileMDP.verified_theorem_4_counterexample
