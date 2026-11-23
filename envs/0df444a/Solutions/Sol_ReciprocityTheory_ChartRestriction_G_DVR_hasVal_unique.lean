-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.DVR.hasVal_unique
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:29:51.873631+00:00
-- url     : https://prove2.me/submissions/22496d37-6613-48b6-8091-eb7afa874a99

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_WchartLePreimage
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_LBLocal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_LBPull
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_LBLocalC
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
set_option autoImplicit false
noncomputable section
open CategoryTheory AlgebraicGeometry TopologicalSpace
namespace ReciprocityTheory.ChartRestriction.G.DVR
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
variable {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] {ϖ : V}
private lemma hasVal_eq_of_hasVal_of_le (hϖ : Irreducible ϖ) {c : FractionRing V} {n m : ℤ}
    (hn : HasVal ϖ c n) (hm : HasVal ϖ c m) (h : m ≤ n) : n = m := by
  obtain ⟨u, hu⟩ := hn
  obtain ⟨u', hu'⟩ := hm
  have hA0 : algebraMap V (FractionRing V) ϖ ≠ 0 := by
    rw [Ne, IsFractionRing.to_map_eq_zero_iff]
    exact hϖ.ne_zero
  have hU0 : algebraMap V (FractionRing V) (u : V) ≠ 0 := by
    rw [Ne, IsFractionRing.to_map_eq_zero_iff]
    exact u.ne_zero
  have e : algebraMap V (FractionRing V) ϖ ^ n * algebraMap V (FractionRing V) (u : V) =
      algebraMap V (FractionRing V) ϖ ^ m * algebraMap V (FractionRing V) (u' : V) :=
    hu.symm.trans hu'
  obtain ⟨d, hd⟩ := Int.eq_ofNat_of_zero_le (sub_nonneg.2 h)
  have h1 : algebraMap V (FractionRing V) ϖ ^ d =
      algebraMap V (FractionRing V) ((u' * u⁻¹ : Vˣ) : V) := by
    rw [← zpow_natCast, ← hd, zpow_sub₀ hA0, Units.val_mul, map_mul, map_units_inv,
      div_eq_iff (zpow_ne_zero _ hA0)]
    field_simp
    linear_combination e
  rw [← map_pow] at h1
  have h2 := IsFractionRing.injective V (FractionRing V) h1
  have hunit : IsUnit (ϖ ^ d) := by
    rw [h2]
    exact Units.isUnit _
  have hd0 : d = 0 := by
    by_contra hd0
    exact hϖ.not_isUnit ((isUnit_pow_iff hd0).1 hunit)
  omega
end ReciprocityTheory.ChartRestriction.G.DVR
end
end

set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.DVR
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
variable {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] {ϖ : V}
namespace ReciprocityTheory.ChartRestriction.G.DVR
theorem _root_.solution (hϖ : Irreducible ϖ) {c : FractionRing V} {n m : ℤ} (hn : HasVal ϖ c n)
    (hm : HasVal ϖ c m) : n = m := by
  rcases le_total m n with h | h
  · exact hasVal_eq_of_hasVal_of_le hϖ hn hm h
  · exact (hasVal_eq_of_hasVal_of_le hϖ hm hn h).symm
end ReciprocityTheory.ChartRestriction.G.DVR
