-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.i2comp_mul_right
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T12:51:49.107368+00:00
-- url     : https://prove2.me/submissions/5c913fc6-56dd-4e7f-806f-e69349eac210

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_DoubleBlock
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_EqSumMultihomogeneousComponents
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_ArakelovGeometry_isMultiHomog_iff_coeff
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_ArakelovGeometry_i2bdeg_apply_add

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
open ReciprocityTheory.ChartRestriction.G.Geo MvPolynomial
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
open Classical
namespace ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
theorem _root_.solution {f : MRing ι} {c : K → ℕ} (hf : IsMultiHomog f c) (a : K → ℕ)
    (g : MRing ι) : i2comp a (g * f) = if c ≤ a then i2comp (a - c) g * f else 0 := by
  rw [isMultiHomog_iff_coeff] at hf
  ext m
  rw [coeff_i2comp]
  split_ifs with hm hca hca
  · rw [coeff_mul, coeff_mul]
    refine Finset.sum_congr rfl fun x hx => ?_
    rw [Finset.HasAntidiagonal.mem_antidiagonal] at hx
    rw [coeff_i2comp]
    by_cases h0 : coeff x.2 f = 0
    · simp [h0]
    · have e2 := hf x.2 h0
      have e : i2bdeg x.1 = a - c := by
        funext k
        have h1 := i2bdeg_apply_add x.1 x.2 k
        rw [hx] at h1
        have h2 := congrFun hm k
        have h3 := congrFun e2 k
        simp only [Pi.sub_apply]
        rw [← h2, h1, h3, Nat.add_sub_cancel]
      rw [if_pos e]
  · rw [coeff_zero, coeff_mul]
    refine Finset.sum_eq_zero fun x hx => ?_
    rw [Finset.HasAntidiagonal.mem_antidiagonal] at hx
    by_cases h0 : coeff x.2 f = 0
    · simp [h0]
    · exfalso
      apply hca
      have e2 := hf x.2 h0
      intro k
      have h1 := i2bdeg_apply_add x.1 x.2 k
      rw [hx] at h1
      have h2 := congrFun hm k
      have h3 := congrFun e2 k
      rw [← h2, h1, h3]
      exact Nat.le_add_left _ _
  · rw [coeff_mul]
    refine (Finset.sum_eq_zero fun x hx => ?_).symm
    rw [Finset.HasAntidiagonal.mem_antidiagonal] at hx
    rw [coeff_i2comp]
    by_cases h0 : coeff x.2 f = 0
    · simp [h0]
    · by_cases e : i2bdeg x.1 = a - c
      · exfalso
        apply hm
        funext k
        have h1 := i2bdeg_apply_add x.1 x.2 k
        rw [hx] at h1
        have h2 := congrFun e k
        have h3 := congrFun (hf x.2 h0) k
        have h4 := hca k
        simp only [Pi.sub_apply] at h2
        rw [h1, h2, h3, Nat.sub_add_cancel h4]
      · simp [e]
  · simp
end ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
