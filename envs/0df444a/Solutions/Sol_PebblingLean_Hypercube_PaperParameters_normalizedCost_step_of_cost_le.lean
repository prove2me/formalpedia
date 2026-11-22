-- Prove2me | solution 1 for PebblingLean.Hypercube.PaperParameters.normalizedCost_step_of_cost_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T06:00:52.176735+00:00
-- url     : https://prove2.me/submissions/416d1610-07d5-43f4-a504-dd515bad713f

module
public import Definitions.Def_LeanPool_PebblingLean_UpperBoundLoss
public import Definitions.Def_LeanPool_PebblingLean_LowerBound
public import Mathlib.Analysis.Complex.ExponentialBounds
public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
public import Definitions.Def_LeanPool_PebblingLean_UpperBoundParameters

set_option autoImplicit true
@[expose] public section
public section
open PebblingLean
open PebblingLean.Hypercube
open PebblingLean.Hypercube.PaperParameters
namespace PebblingLean.Hypercube.PaperParameters
theorem _root_.solution {K : ℝ} {costBound : ℕ → ℕ} {n : ℕ}
    (hsplit : splitA K n + splitM K n = n)
    (hcostReal :
      (costBound n : ℝ) ≤
        (1 + loss n) * (((4 : ℝ) / 3) ^ splitA K n) *
          (costBound (splitM K n) : ℝ)) :
    normalizedCost costBound n ≤
      (1 + loss n) * normalizedCost costBound (splitM K n) := by
  unfold normalizedCost
  have hbase_pos : 0 < ((4 : ℝ) / 3) := by norm_num
  have hpow_n_pos : 0 < (((4 : ℝ) / 3) ^ n) := pow_pos hbase_pos n
  have hdiv := div_le_div_of_nonneg_right hcostReal hpow_n_pos.le
  have hpow_split : (((4 : ℝ) / 3) ^ n) =
      (((4 : ℝ) / 3) ^ splitA K n) * (((4 : ℝ) / 3) ^ splitM K n) := by
    rw [← pow_add, hsplit]
  calc
    (costBound n : ℝ) / (((4 : ℝ) / 3) ^ n)
        ≤ ((1 + loss n) * (((4 : ℝ) / 3) ^ splitA K n) *
          (costBound (splitM K n) : ℝ)) / (((4 : ℝ) / 3) ^ n) := hdiv
    _ = (1 + loss n) * ((costBound (splitM K n) : ℝ) /
          (((4 : ℝ) / 3) ^ splitM K n)) := by
          rw [hpow_split]
          field_simp [pow_ne_zero _ hbase_pos.ne']
end PebblingLean.Hypercube.PaperParameters
