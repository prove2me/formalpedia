-- Prove2me | solution 1 for PersonalizedAssortment.IB.lemma5_ratio_monotone
-- status  : ACCEPTED   (prove)
-- author  : @涼宮 ハルヒ
-- created : 2026-10-24T03:35:35.459215+00:00
-- url     : https://prove2.me/submissions/f76455b3-0998-4da7-a19a-ba0e50e39d77

import Definitions.Def_PersonalizedAssortment_IB_PenaltyFunction
import Mathlib.Analysis.Convex.Function
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith

set_option autoImplicit false
open PersonalizedAssortment.IB

theorem solution (Ψ : ℝ → ℝ) (hΨ : IsPenaltyFunction Ψ)
    (hconc : ConcaveOn ℝ (Set.Icc 0 1) Ψ) (hdiff : DifferentiableOn ℝ Ψ (Set.Icc 0 1))
    (hdiff2 : DifferentiableOn ℝ (derivWithin Ψ (Set.Icc 0 1)) (Set.Icc 0 1)) :
    MonotoneOn (fun x : ℝ => (1 - x) / (2 - x - Ψ x)) (Set.Ico 0 1) := by
  intro x hx y hy hxy
  have hx' : x ∈ Set.Icc (0 : ℝ) 1 := ⟨hx.1, hx.2.le⟩
  have hy' : y ∈ Set.Icc (0 : ℝ) 1 := ⟨hy.1, hy.2.le⟩
  have hden : 0 < 1 - x := sub_pos.mpr hx.2
  have hweights : (1 - y) / (1 - x) + (y - x) / (1 - x) = 1 := by
    field_simp
    ring
  have hpoint : ((1 - y) / (1 - x)) * x + ((y - x) / (1 - x)) * 1 = y := by
    field_simp
    ring
  have hchord := hconc.2 hx' (show (1 : ℝ) ∈ Set.Icc 0 1 by simp)
    (div_nonneg (sub_nonneg.mpr hy.2.le) hden.le)
    (div_nonneg (sub_nonneg.mpr hxy) hden.le) hweights
  simp only [smul_eq_mul, hΨ.2.2.2, hpoint] at hchord
  have hchord' : (1 - y) * Ψ x + (y - x) ≤ (1 - x) * Ψ y := by
    have hm := (mul_le_mul_of_nonneg_left hchord hden.le)
    field_simp at hm
    nlinarith [hm]
  have hpx := (hΨ.1 hx').2
  have hpy := (hΨ.1 hy').2
  have hdx : 0 < 2 - x - Ψ x := by linarith [hx.2]
  have hdy : 0 < 2 - y - Ψ y := by linarith [hy.2]
  apply (div_le_div_iff₀ hdx hdy).mpr
  nlinarith [hchord']

#print axioms solution
