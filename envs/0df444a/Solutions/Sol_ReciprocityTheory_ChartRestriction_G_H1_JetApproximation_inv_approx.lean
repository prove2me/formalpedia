-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.H1.JetApproximation.inv_approx
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T13:07:49.122054+00:00
-- url     : https://prove2.me/submissions/a2420e27-4eb1-4ffe-8fc9-0352f88df731

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FirstCohomology_JetApproximation
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_H1_JetApproximation_one_le_pow
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_H1_JetApproximation_pow_mono

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.H1 ReciprocityTheory.ChartRestriction.G.H1.JetApproximation
variable {F R : Type*} [Field F] [CommRing R] [Algebra F R]
namespace ReciprocityTheory.ChartRestriction.G.H1.JetApproximation
theorem _root_.solution {V : Submodule F R} (h1 : 1 ≤ V) {m : Ideal R} (hm : ∀ x ∈ m, ¬ IsUnit x)
    (hres : ∀ f : R, ∃ c : F, f - algebraMap F R c ∈ m) (D n : ℕ) (u : Rˣ) (hu : (u : R) ∈ V ^ n) :
    ∃ w ∈ V ^ (n * D), ((u⁻¹ : Rˣ) : R) - w ∈ m ^ (D + 1) := by
  obtain ⟨c, hc⟩ := hres u
  have hc0 : c ≠ 0 := by
    rintro rfl
    rw [map_zero, sub_zero] at hc
    exact hm _ hc u.isUnit
  set a : R := algebraMap F R c⁻¹
  have ha : a * algebraMap F R c = 1 := by rw [← map_mul, inv_mul_cancel₀ hc0, map_one]
  set x : R := -(a * u - 1)
  have hxm : x ∈ m := by
    have : a * u - 1 = a * ((u : R) - algebraMap F R c) := by rw [mul_sub, ha]
    rw [show x = -(a * u - 1) from rfl, this]
    exact m.neg_mem (m.mul_mem_left a hc)
  have hxV : x ∈ V ^ n := by
    refine (V ^ n).neg_mem ((V ^ n).sub_mem ?_ (Submodule.one_le.1 (one_le_pow h1 n)))
    rw [show a * (u : R) = c⁻¹ • (u : R) from (Algebra.smul_def _ _).symm]
    exact (V ^ n).smul_mem _ hu
  refine ⟨a * ∑ e ∈ Finset.range (D + 1), x ^ e, ?_, ?_⟩
  · rw [show a * ∑ e ∈ Finset.range (D + 1), x ^ e = c⁻¹ • ∑ e ∈ Finset.range (D + 1), x ^ e from
      (Algebra.smul_def _ _).symm]
    refine (V ^ (n * D)).smul_mem _ (Submodule.sum_mem _ fun e he => ?_)
    have hx := Submodule.pow_mem_pow (V ^ n) hxV e
    rw [← pow_mul] at hx
    exact pow_mono h1 (Nat.mul_le_mul_left n (Nat.lt_succ_iff.1 (Finset.mem_range.1 he))) hx
  · have hau : a * u = 1 - x := by rw [show x = -(a * u - 1) from rfl]; ring
    have hgeom : (u : R) * (a * ∑ e ∈ Finset.range (D + 1), x ^ e) = 1 - x ^ (D + 1) := by
      rw [← mul_assoc, mul_comm (u : R) a, hau, mul_neg_geom_sum]
    have : ((u⁻¹ : Rˣ) : R) - a * ∑ e ∈ Finset.range (D + 1), x ^ e = ((u⁻¹ : Rˣ) : R) * x ^ (D + 1) := by
      have e1 : ((u⁻¹ : Rˣ) : R) * u = 1 := u.inv_mul
      calc ((u⁻¹ : Rˣ) : R) - a * ∑ e ∈ Finset.range (D + 1), x ^ e
          = ((u⁻¹ : Rˣ) : R) * (1 - (u : R) * (a * ∑ e ∈ Finset.range (D + 1), x ^ e)) := by
            rw [mul_sub, mul_one, ← mul_assoc, e1, one_mul]
        _ = _ := by rw [hgeom]; ring
    rw [this]
    exact (m ^ (D + 1)).mul_mem_left _ (Ideal.pow_mem_pow hxm _)
end ReciprocityTheory.ChartRestriction.G.H1.JetApproximation
