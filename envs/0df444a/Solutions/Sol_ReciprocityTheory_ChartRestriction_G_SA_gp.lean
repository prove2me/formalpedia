-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.SA.gp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T13:33:02.827346+00:00
-- url     : https://prove2.me/submissions/7f7c4a2a-efc0-453f-88d0-d62592163af7

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_StrongApproximation_ExistsMaxOfNotCoprime
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_SA_norm_zero_of_not_unit

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.SA
variable {K : Type*} [CommRing K] {σ : K →+* K} (hσ : ∀ x, σ (σ x) = x)
  (hfix : ∀ x, σ x = x → x ≠ 0 → IsUnit x)
include hσ hfix
namespace ReciprocityTheory.ChartRestriction.G.SA
theorem _root_.solution [IsReduced K] (h2 : IsUnit (2 : K)) {δ : K} (hδ : IsUnit δ) (hσδ : σ δ = -δ) {x y : K}
    (hxy : IsCoprime x y) :
    IsUnit x ∨ IsUnit (x + δ * y) ∨ IsUnit (x + (-1) * δ * y) := by
  by_contra hcon
  push_neg at hcon
  obtain ⟨h1, h2', h3⟩ := hcon
  have e1 := norm_zero_of_not_unit hσ hfix h1
  have e2 := norm_zero_of_not_unit hσ hfix h2'
  have e3 := norm_zero_of_not_unit hσ hfix h3
  simp only [map_add, map_mul, hσδ, map_neg, map_one] at e2 e3
  obtain ⟨a, b, hab⟩ := hxy
  have hab' : σ a * σ x + σ b * σ y = 1 := by
    have := congrArg σ hab
    simpa only [map_add, map_mul, map_one] using this
  have hyy0 : (2 * δ ^ 2) * (y * σ y) = 0 := by linear_combination 2 * e1 - e2 - e3
  have hyy : y * σ y = 0 := ((h2.mul (hδ.pow 2)).mul_right_eq_zero).mp hyy0
  have hxy0 : (2 * δ) * (y * σ x - x * σ y) = 0 := by linear_combination e2 - e3
  have hxy' : y * σ x - x * σ y = 0 := ((h2.mul hδ).mul_right_eq_zero).mp hxy0
  have key : (a * σ b + b * σ a) * (x * σ y) = 1 := by
    linear_combination (σ a * σ x + σ b * σ y) * hab + hab' - σ a * b * hxy' - a * σ a * e1 -
      b * σ b * hyy
  have hu : IsUnit (x * σ y) := isUnit_iff_exists_inv.mpr ⟨_, by rw [mul_comm]; exact key⟩
  have hsq : (x * σ y) * (x * σ y) = 0 := by
    linear_combination (y * σ y) * e1 - (x * σ y) * hxy'
  have h0 : IsUnit (0 : K) := by
    have := hu.mul hu
    rwa [hsq] at this
  haveI := subsingleton_of_zero_eq_one (isUnit_zero_iff.mp h0)
  exact h1 (isUnit_of_subsingleton x)
end ReciprocityTheory.ChartRestriction.G.SA
