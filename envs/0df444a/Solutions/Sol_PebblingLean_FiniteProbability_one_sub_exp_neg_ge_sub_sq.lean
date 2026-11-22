-- Prove2me | solution 1 for PebblingLean.FiniteProbability.one_sub_exp_neg_ge_sub_sq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T05:48:57.70214+00:00
-- url     : https://prove2.me/submissions/51e67a96-611a-4a3f-a6c6-178f92f919e7

module
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Definitions.Def_LeanPool_PebblingLean_FiniteProbability
public import Mathlib.Analysis.Convex.Jensen
public import Mathlib.Analysis.Convex.SpecificFunctions.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
public import Mathlib.Tactic.Positivity.Finset
public import Definitions.Def_LeanPool_PebblingLean_Concentration

set_option autoImplicit true
@[expose] public section
public section
open PebblingLean
open PebblingLean.FiniteProbability
variable {Ω : Type*}
namespace PebblingLean.FiniteProbability
theorem _root_.solution {x : ℝ} (hx : 0 ≤ x) :
    x - x ^ 2 ≤ 1 - Real.exp (-x) := by
  have hxden : 0 < 1 + x := by positivity
  have hexp_inv : Real.exp (-x) ≤ (1 + x)⁻¹ := by
    have h := Real.add_one_le_exp x
    have hpos : 0 < Real.exp x := Real.exp_pos x
    have hinv := (inv_le_inv₀ hpos hxden).mpr (by simpa [add_comm] using h)
    simpa [Real.exp_neg] using hinv
  have hpoly : (1 + x)⁻¹ ≤ 1 - x + x ^ 2 := by
    rw [← one_div, div_le_iff₀ hxden]
    nlinarith [sq_nonneg x, mul_nonneg hx (sq_nonneg x)]
  linarith
end PebblingLean.FiniteProbability
