-- Prove2me | solution 1 for PebblingLean.FiniteProbability.exp_chord_quadratic_optimized
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T05:48:59.025501+00:00
-- url     : https://prove2.me/submissions/7f1283bd-43d6-4910-888d-095ecf77580b

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
theorem _root_.solution {T gap B mu lam : ℝ}
    (hB : 0 < B) (hmu : 0 < mu) (hgap : 0 ≤ gap)
    (hmean : T + gap ≤ mu)
    (hlam : lam = gap / (2 * B * mu)) :
    Real.exp (lam * T - (lam - lam ^ 2 * B) * mu) ≤
      Real.exp (-(gap ^ 2 / (4 * B * mu))) := by
  apply Real.exp_le_exp.mpr
  subst lam
  have hden_pos : 0 < 2 * B * mu := by positivity
  have hBmu_pos : 0 < B * mu := mul_pos hB hmu
  have hgap_le : gap ≤ mu - T := by linarith
  have hmain :
      gap * T ≤ gap * mu - gap ^ 2 := by
    nlinarith [mul_le_mul_of_nonneg_left hgap_le hgap]
  field_simp [hden_pos.ne', hB.ne', hmu.ne', hBmu_pos.ne']
  ring_nf
  nlinarith
end PebblingLean.FiniteProbability
