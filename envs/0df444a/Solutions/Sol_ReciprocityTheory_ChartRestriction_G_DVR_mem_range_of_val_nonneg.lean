-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.DVR.mem_range_of_val_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-27T05:34:53.223739+00:00
-- url     : https://prove2.me/submissions/fd672b00-2983-4b27-8b73-6b194343f7d5

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_ThickKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_SectionScalarValuation
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_ValuationMultiplicationInvariance
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_NuExtA

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.DVR
open AlgebraicGeometry CategoryTheory Limits TopologicalSpace Opposite ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
  ReciprocityTheory.ChartRestriction.G.Out
variable {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
namespace ReciprocityTheory.ChartRestriction.G.DVR
theorem _root_.solution {ϖ : V} (hϖ : Irreducible ϖ) {v : AddValuation (FractionRing V) (WithTop ℚ)}
    (hv : ValOver ϖ (FractionRing V) v) (c : FractionRing V) (hc : 0 ≤ v c) :
    c ∈ (algebraMap V (FractionRing V)).range := by
  classical
  by_cases hc0 : c = 0
  · exact ⟨0, by rw [hc0, map_zero]⟩
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := V) c
  have ha : a ≠ 0 := by
    rintro rfl
    exact hc0 (by simp)
  have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
  obtain ⟨n1, u1, hu1⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible ha hϖ
  obtain ⟨n2, u2, hu2⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hb0 hϖ
  have hϖ0 : algebraMap V (FractionRing V) ϖ ≠ 0 :=
    (IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors (mem_nonZeroDivisors_of_ne_zero hϖ.ne_zero))
  have hu2' : algebraMap V (FractionRing V) (u2 : V) ≠ 0 :=
    IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors (mem_nonZeroDivisors_of_ne_zero u2.ne_zero)
  set w : Vˣ := u1 * u2⁻¹ with hw
  have hval : HasVal ϖ (algebraMap V (FractionRing V) a / algebraMap V (FractionRing V) b) ((n1 : ℤ) - n2) := by
    refine ⟨w, ?_⟩
    rw [hu1, hu2, hw, zpow_sub₀ hϖ0, zpow_natCast, zpow_natCast]
    simp only [map_mul, map_pow, Units.val_mul]
    have hinv : algebraMap V (FractionRing V) ((u2⁻¹ : Vˣ) : V) = (algebraMap V (FractionRing V) (u2 : V))⁻¹ := by
      exact map_units_inv (algebraMap V (FractionRing V)) u2
    rw [hinv]
    field_simp
  have hv1 := hv _ _ hval
  simp only [Algebra.algebraMap_self, RingHom.id_apply] at hv1
  rw [hv1] at hc
  have hn : (0 : ℤ) ≤ (n1 : ℤ) - n2 := by
    have : ((0 : ℚ) : WithTop ℚ) ≤ (((n1 : ℤ) - n2 : ℤ) : ℚ) := by simpa using hc
    have h2 : (0 : ℚ) ≤ (((n1 : ℤ) - n2 : ℤ) : ℚ) := WithTop.coe_le_coe.mp this
    exact_mod_cast h2
  obtain ⟨k, hk⟩ := Int.eq_ofNat_of_zero_le hn
  obtain ⟨w', hw'⟩ := hval
  refine ⟨ϖ ^ k * (w' : V), ?_⟩
  rw [hw', hk, zpow_natCast, map_mul, map_pow]
end ReciprocityTheory.ChartRestriction.G.DVR
