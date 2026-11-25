-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Geo.ratHom_isLocalization
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T13:12:33.801862+00:00
-- url     : https://prove2.me/submissions/fe29f133-9455-40c6-90a6-e6c19c2e96a5

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterGoodA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterGoodB
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_qmap_injective
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_exists_int_mul_eq_qmap
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_exists_int_mul_mem_of_mem_qIdeal
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_ratHom_mk

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo
open MvPolynomial
noncomputable section
variable {σ : Type}
namespace ReciprocityTheory.ChartRestriction.G.Geo
theorem _root_.solution (P : Ideal (MvPolynomial σ ℤ)) :
    letI := (ratHom P).toAlgebra
    IsLocalization (Algebra.algebraMapSubmonoid (MvPolynomial σ ℤ ⧸ P) (nonZeroDivisors ℤ))
      (MvPolynomial σ ℚ ⧸ qIdeal P) := by
  let _ := (ratHom P).toAlgebra
  have hcast : ∀ n : ℤ, algebraMap (MvPolynomial σ ℤ ⧸ P) (MvPolynomial σ ℚ ⧸ qIdeal P)
      (algebraMap ℤ (MvPolynomial σ ℤ ⧸ P) n) = algebraMap ℚ (MvPolynomial σ ℚ ⧸ qIdeal P) n := by
    intro n
    rw [eq_intCast, map_intCast, map_intCast]
  refine ⟨?_, ?_, ?_⟩
  · rintro ⟨y, hy⟩
    obtain ⟨n, hn, rfl⟩ := Submonoid.mem_map.mp hy
    rw [hcast]
    exact (IsUnit.mk0 (n : ℚ) (by exact_mod_cast nonZeroDivisors.ne_zero hn)).map _
  · intro z
    obtain ⟨q, rfl⟩ := Ideal.Quotient.mk_surjective z
    obtain ⟨D, hD, q', hq'⟩ := exists_int_mul_eq_qmap q
    refine ⟨⟨Ideal.Quotient.mk P q', ⟨algebraMap ℤ _ D,
      Submonoid.mem_map.mpr ⟨D, mem_nonZeroDivisors_of_ne_zero hD, rfl⟩⟩⟩, ?_⟩
    change _ * algebraMap (MvPolynomial σ ℤ ⧸ P) _ (algebraMap ℤ _ D) = ratHom P (Ideal.Quotient.mk P q')
    rw [hcast, ratHom_mk, ← hq', mul_comm, map_mul]
    congr 1
  · intro x y hxy
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective y
    change ratHom P _ = ratHom P _ at hxy
    rw [ratHom_mk, ratHom_mk, Ideal.Quotient.eq, ← map_sub] at hxy
    obtain ⟨N, hN, h, hh, e⟩ := exists_int_mul_mem_of_mem_qIdeal P hxy
    have hNab : (N : MvPolynomial σ ℤ) * (a - b) = h := by
      apply qmap_injective
      rw [map_mul, map_intCast, e]
    refine ⟨⟨algebraMap ℤ _ N, Submonoid.mem_map.mpr ⟨N, mem_nonZeroDivisors_of_ne_zero hN, rfl⟩⟩, ?_⟩
    change algebraMap ℤ _ N * Ideal.Quotient.mk P a = algebraMap ℤ _ N * Ideal.Quotient.mk P b
    rw [← sub_eq_zero, ← mul_sub, ← map_sub, eq_intCast, ← map_intCast (Ideal.Quotient.mk P), ← map_mul,
      hNab, Ideal.Quotient.eq_zero_iff_mem]
    exact hh
end ReciprocityTheory.ChartRestriction.G.Geo
