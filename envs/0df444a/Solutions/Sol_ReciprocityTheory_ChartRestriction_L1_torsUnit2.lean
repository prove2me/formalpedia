-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.L1.torsUnit2
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T14:01:02.147802+00:00
-- url     : https://prove2.me/submissions/929c0dfe-3901-4ef8-9d53-08fb10dc94da

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_RedDefs
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_StatementK
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_FormalGroupPointsNoPrimeToPTorsion
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_TorInt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_TorsUnit2
import Theorems.Thm_Formalism_ELL_FormalGroupPointsTorsion_dom
import Theorems.Thm_Formalism_ELL_FormalGroupPointsTorsion_sub_lt
import Theorems.Thm_Formalism_ELL_formal_group_points_no_prime_to_p_torsion
import Theorems.Thm_Formalism_ELL_torsionIntegral_of


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical
open Formalism.L2.Th1.CM Formalism.L2.Th1.F WeierstrassCurve
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.L1
namespace ReciprocityTheory.ChartRestriction.L1
theorem _root_.solution (K : Type) [NormedField K] [IsUltrametricDist K] (g2 g3 : K) (h2 : ‖(2 : K)‖ = 1)
    (h3 : ‖(3 : K)‖ = 1) (hg2 : ‖g2‖ ≤ 1) (hg3 : ‖g3‖ < 1) (hΔ : ‖g2 ^ 3 - 27 * g3 ^ 2‖ = 1)
    (n : ℕ) (hn : ‖(n : K)‖ = 1) (hen : ¬ 2 ∣ n) (x y : K)
    (h : (Formalism.L2.Th1.A.shortW g2 g3).toAffine.Nonsingular x y) (hP : n • (Affine.Point.some x y h) = 0) : ‖x‖ = 1 := by
  have n4 : ‖(4 : K)‖ = 1 := by
    rw [show (4 : K) = 2 * 2 by norm_num, norm_mul, h2]; norm_num
  have h40 : (4 : K) ≠ 0 := by
    intro h0; rw [h0, norm_zero] at n4; exact zero_ne_one n4
  have h20 : (2 : K) ≠ 0 := by
    intro h0; rw [h0, norm_zero] at h2; exact zero_ne_one h2
  have hW : Formalism.ELL.IntegralModel (Formalism.L2.Th1.A.shortW g2 g3) := by
    refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> simp [Formalism.L2.Th1.A.shortW, n4, hg2, hg3.le]
  have hD : ‖(Formalism.L2.Th1.A.shortW g2 g3).Δ‖ = 1 := by
    have : (Formalism.L2.Th1.A.shortW g2 g3).Δ = g2 ^ 3 - 27 * g3 ^ 2 := by
      simp only [WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄,
        WeierstrassCurve.b₆, WeierstrassCurve.b₈, Formalism.L2.Th1.A.shortW]
      field_simp
      ring
    rw [this, hΔ]

  have n27 : ‖(27 : K)‖ = 1 := by
    rw [show (27 : K) = 3 * 3 * 3 by norm_num, norm_mul, norm_mul, h3]; norm_num
  have hg2' : ‖g2‖ = 1 := by
    have hs : ‖27 * g3 ^ 2‖ < 1 := by
      rw [norm_mul, n27, one_mul, norm_pow]
      exact pow_lt_one₀ (norm_nonneg _) hg3 (by norm_num)
    have h1 : ‖g2 ^ 3‖ = 1 := by
      have e : g2 ^ 3 = (g2 ^ 3 - 27 * g3 ^ 2) + 27 * g3 ^ 2 := by ring
      rw [e, Formalism.ELL.FormalGroupPointsTorsion.dom (by rw [hΔ]; exact hs), hΔ]
    rw [norm_pow] at h1
    exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) (by norm_num)).1 h1
  obtain ⟨hx, -⟩ := Formalism.ELL.torsionIntegral_of Formalism.ELL.formal_group_points_no_prime_to_p_torsion K _ hW hD n hn x y h hP
  by_contra hne
  have hx1 : ‖x‖ < 1 := lt_of_le_of_ne hx hne
  have heq : y ^ 2 = x ^ 3 - g2 / 4 * x - g3 / 4 := by
    have := (Affine.equation_iff x y).1 h.1
    simp only [Formalism.L2.Th1.A.shortW] at this
    linear_combination this
  have hy1 : ‖y‖ < 1 := by
    have : ‖y ^ 2‖ < 1 := by
      rw [heq]
      refine Formalism.ELL.FormalGroupPointsTorsion.sub_lt (Formalism.ELL.FormalGroupPointsTorsion.sub_lt ?_ ?_) ?_
      · rw [norm_pow]; exact pow_lt_one₀ (norm_nonneg _) hx1 (by norm_num)
      · rw [norm_mul, norm_div, n4, hg2']; simpa using hx1
      · rw [norm_div, n4]; simpa using hg3
    rw [norm_pow] at this
    by_contra hc
    push Not at hc
    exact absurd this (not_lt.2 (one_le_pow₀ hc))

  have hQ : Formalism.ELL.InFormalGroupPoints (Affine.Point.some x y h + Affine.Point.some x y h) := by
    by_cases hy : y = (Formalism.L2.Th1.A.shortW g2 g3).toAffine.negY x y
    · rw [Affine.Point.add_self_of_Y_eq hy, Affine.Point.zero_def]; trivial
    · rw [Affine.Point.add_self_of_Y_ne hy]
      show 1 < ‖_‖
      have hy0 : y ≠ 0 := by
        rintro rfl
        exact hy (by simp [Affine.negY, Formalism.L2.Th1.A.shortW])
      rw [Affine.slope_of_Y_ne rfl hy]
      simp only [Affine.addX, Affine.negY, Formalism.L2.Th1.A.shortW]
      have e : ((3 * x ^ 2 + 2 * 0 * x + -g2 / 4 - 0 * y) / (y - (-y - 0 * x - 0))) ^ 2 +
          0 * ((3 * x ^ 2 + 2 * 0 * x + -g2 / 4 - 0 * y) / (y - (-y - 0 * x - 0))) - 0 - x - x
          = ((-(g2 / 4) + 3 * x ^ 2) / (2 * y)) ^ 2 + (-x - x) := by
        have : y - (-y - 0 * x - 0) = 2 * y := by ring
        rw [this]; ring
      rw [e]
      have hnum : ‖-(g2 / 4) + 3 * x ^ 2‖ = 1 := by
        have ha : ‖-(g2 / 4)‖ = 1 := by rw [norm_neg, norm_div, n4, hg2']; norm_num
        rw [Formalism.ELL.FormalGroupPointsTorsion.dom, ha]
        rw [ha, norm_mul, h3, one_mul, norm_pow]
        exact pow_lt_one₀ (norm_nonneg _) hx1 (by norm_num)
      have hyp : 0 < ‖y‖ := norm_pos_iff.2 hy0
      have hl : 1 < ‖((-(g2 / 4) + 3 * x ^ 2) / (2 * y)) ^ 2‖ := by
        rw [norm_pow, norm_div, hnum, norm_mul, h2, one_mul]
        exact one_lt_pow₀ ((one_lt_div hyp).2 hy1) (by norm_num)
      have hs : ‖-x - x‖ < 1 :=
        Formalism.ELL.FormalGroupPointsTorsion.sub_lt (by rwa [norm_neg]) hx1
      rw [Formalism.ELL.FormalGroupPointsTorsion.dom (hs.trans hl)]
      exact hl
  have hQ0 : Affine.Point.some x y h + Affine.Point.some x y h = 0 := by
    refine Formalism.ELL.formal_group_points_no_prime_to_p_torsion K _ hW hD n hn _ hQ ?_
    rw [nsmul_add, hP, add_zero]
  obtain ⟨k, rfl⟩ : ∃ k, n = 2 * k + 1 := by
    have := Nat.odd_iff.2 (by omega : n % 2 = 1)
    exact this
  refine Affine.Point.some_ne_zero h ?_
  rw [add_nsmul, one_nsmul, mul_comm, mul_nsmul', two_nsmul, hQ0, nsmul_zero, zero_add] at hP
  exact hP
end ReciprocityTheory.ChartRestriction.L1
