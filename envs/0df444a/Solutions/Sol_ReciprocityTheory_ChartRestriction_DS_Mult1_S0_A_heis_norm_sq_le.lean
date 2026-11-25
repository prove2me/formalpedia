-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.Mult1.S0.A.heis_norm_sq_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T12:13:02.471107+00:00
-- url     : https://prove2.me/submissions/eb5b5b1b-4efc-4953-8d52-d7cd0136b475

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_MultiplicityOne_HermitianMeasures_NHeisInt

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Matrix
open scoped ENNReal NNReal InnerProductSpace
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.Mult1 ReciprocityTheory.ChartRestriction.DS.Mult1.S0 ReciprocityTheory.ChartRestriction.DS.Mult1.S0.A
namespace ReciprocityTheory.ChartRestriction.DS.Mult1.S0.A
theorem _root_.solution (m : ℕ) (x : (Fin m → ℂ) × ℝ) :
    ‖x‖ ^ 2 ≤ ∑ i, Complex.normSq (x.1 i) + x.2 ^ 2 := by
  have hS : 0 ≤ ∑ i, Complex.normSq (x.1 i) :=
    Finset.sum_nonneg fun i _ => Complex.normSq_nonneg _
  have hT : 0 ≤ ∑ i, Complex.normSq (x.1 i) + x.2 ^ 2 := by positivity
  have h1 : ‖x.1‖ ≤ Real.sqrt (∑ i, Complex.normSq (x.1 i) + x.2 ^ 2) := by
    refine (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)).2 (fun i => ?_)
    calc ‖x.1 i‖ = Real.sqrt (‖x.1 i‖ ^ 2) := (Real.sqrt_sq (norm_nonneg _)).symm
      _ ≤ Real.sqrt (∑ i, Complex.normSq (x.1 i) + x.2 ^ 2) := by
        apply Real.sqrt_le_sqrt
        have hi : Complex.normSq (x.1 i) ≤ ∑ j, Complex.normSq (x.1 j) :=
          Finset.single_le_sum (f := fun j => Complex.normSq (x.1 j))
            (fun j _ => Complex.normSq_nonneg _) (Finset.mem_univ i)
        rw [← Complex.normSq_eq_norm_sq]
        nlinarith [sq_nonneg x.2]
  have h2 : ‖x.2‖ ≤ Real.sqrt (∑ i, Complex.normSq (x.1 i) + x.2 ^ 2) := by
    calc ‖x.2‖ = Real.sqrt (x.2 ^ 2) := by rw [Real.sqrt_sq_eq_abs, Real.norm_eq_abs]
      _ ≤ _ := Real.sqrt_le_sqrt (by linarith)
  have h3 : ‖x‖ ≤ Real.sqrt (∑ i, Complex.normSq (x.1 i) + x.2 ^ 2) := by
    rw [Prod.norm_def]; exact max_le h1 h2
  calc ‖x‖ ^ 2 ≤ (Real.sqrt (∑ i, Complex.normSq (x.1 i) + x.2 ^ 2)) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) h3 2
    _ = _ := Real.sq_sqrt hT
end ReciprocityTheory.ChartRestriction.DS.Mult1.S0.A
