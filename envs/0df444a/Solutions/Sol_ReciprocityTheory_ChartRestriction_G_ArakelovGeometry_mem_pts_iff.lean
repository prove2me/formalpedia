-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.mem_pts_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T12:58:36.882911+00:00
-- url     : https://prove2.me/submissions/7b22ef93-cc9a-45ad-9110-7b6ec326a778

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_HSClosing
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_LemCone
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterGoodB
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_StepTStA
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_ArakelovGeometry_aeval_int_eq
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_ArakelovGeometry_aeval_qmap
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_coeff_coneMap
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_coneMap_of_isHomogeneous


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
variable {J : Type} [Fintype J] {Ω : Type*} [Field Ω] [CharZero Ω]
namespace ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
theorem _root_.solution (v : J → Ω) (z : J → ℂ) :
    z ∈ pts (coordIdeal ℤ v) ↔ z ≠ 0 ∧ ∀ (n : ℕ) (g : MvPolynomial J ℚ), g.IsHomogeneous n →
      aeval v g = 0 → aeval z g = 0 := by
  classical
  simp only [pts, conePts, Set.mem_setOf_eq, coordIdeal, RingHom.mem_ker, aeval_int_eq]
  refine and_congr_right fun _ => ⟨fun H n g hg hv => ?_, fun H f hf => ?_⟩
  · obtain ⟨b, hb⟩ := IsLocalization.exist_integer_multiples_of_finset (nonZeroDivisors ℤ)
      (g.support.image fun m => g.coeff m)
    have hr' : ∀ m, ∃ r : ℤ, (r : ℚ) = ((b : ℤ) : ℚ) * g.coeff m := by
      intro m
      by_cases hm : m ∈ g.support
      · obtain ⟨r, hr⟩ := hb _ (Finset.mem_image_of_mem _ hm)
        exact ⟨r, by simpa [Algebra.smul_def] using hr⟩
      · rw [mem_support_iff, not_not] at hm
        exact ⟨0, by simp [hm]⟩
    choose r hr using hr'
    obtain ⟨f, hfdef⟩ : ∃ f : MvPolynomial J ℤ, f = ∑ m ∈ g.support, monomial m (r m) := ⟨_, rfl⟩
    have hfg : qmap f = C ((b : ℤ) : ℚ) * g := by
      ext m
      rw [coeff_C_mul, ← hr m]
      simp only [qmap, coeff_map, hfdef, coeff_sum, MvPolynomial.coeff_monomial, Finset.sum_ite_eq', Finset.sum_ite_eq]
      split_ifs with hm
      · simp
      · rw [mem_support_iff, not_not] at hm
        rw [map_zero, hr m, hm, mul_zero]
    have hfh : f.IsHomogeneous n := by
      intro d hd
      apply hg
      intro h0
      apply hd
      have h1 := congrArg (coeff d) hfg
      rw [coeff_C_mul, h0, mul_zero] at h1
      simp only [qmap, coeff_map] at h1
      simpa using h1
    have hvf : aeval v f = 0 := by
      rw [← aeval_qmap, hfg, map_mul, hv, mul_zero]
    have hz := H f (by rw [coneMap_of_isHomogeneous (x := v) (hf := hfh), hvf, map_zero, zero_mul])
    rw [← aeval_qmap, hfg, map_mul, aeval_C] at hz
    have hb0 : (b : ℤ) ≠ 0 := nonZeroDivisors.coe_ne_zero b
    rcases mul_eq_zero.mp hz with h | h
    · exact absurd (by simpa using h) hb0
    · exact h
  · have hk : ∀ k, aeval z (homogeneousComponent k f) = 0 := by
      intro k
      have h1 : aeval v (homogeneousComponent k f) = 0 := by
        rw [← coeff_coneMap, hf, Polynomial.coeff_zero]
      have h2 := H k (qmap (homogeneousComponent k f)) ((homogeneousComponent_isHomogeneous k f).map _)
        (by rw [aeval_qmap, h1])
      rwa [aeval_qmap] at h2
    rw [← sum_homogeneousComponent (φ := f), map_sum]
    exact Finset.sum_eq_zero fun k _ => hk k
end ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
