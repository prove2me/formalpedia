-- Prove2me | solution 1 for PebblingLean.FiniteProbability.pow_le_exp_neg_mul_of_le_one_sub
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T05:49:35.482048+00:00
-- url     : https://prove2.me/submissions/3e6948c4-440f-488c-8a42-599da33fb4fd

module
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Definitions.Def_LeanPool_PebblingLean_FiniteProbability
public import Mathlib.Analysis.Convex.Jensen
public import Mathlib.Analysis.Convex.SpecificFunctions.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
public import Mathlib.Tactic.Positivity.Finset
public import Definitions.Def_LeanPool_PebblingLean_Concentration
public import Theorems.Thm_PebblingLean_FiniteProbability_one_sub_le_exp_neg

set_option autoImplicit true
@[expose] public section
public section
open PebblingLean
open PebblingLean.FiniteProbability
variable {Ω : Type*}
namespace PebblingLean.FiniteProbability
theorem _root_.solution {a u : ℝ} (N : ℕ)
    (ha_nonneg : 0 ≤ a) (ha_le : a ≤ 1 - u) :
    a ^ N ≤ Real.exp (-((N : ℝ) * u)) := by
  have ha_exp : a ≤ Real.exp (-u) := ha_le.trans (one_sub_le_exp_neg u)
  induction N with
  | zero =>
      simp
  | succ N ih =>
      have hexp_nonneg : 0 ≤ Real.exp (-((N : ℝ) * u)) := Real.exp_nonneg _
      calc
        a ^ (N + 1) = a ^ N * a := by
          rw [pow_succ]
        _ ≤ Real.exp (-((N : ℝ) * u)) * Real.exp (-u) := by
          exact mul_le_mul ih ha_exp ha_nonneg hexp_nonneg
        _ = Real.exp (-(((N + 1 : ℕ) : ℝ) * u)) := by
          rw [← Real.exp_add]
          norm_num
          ring_nf
end PebblingLean.FiniteProbability
