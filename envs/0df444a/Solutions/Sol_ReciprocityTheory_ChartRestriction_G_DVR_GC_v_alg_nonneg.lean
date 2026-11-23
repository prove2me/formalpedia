-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.DVR.GC.v_alg_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:15:03.141741+00:00
-- url     : https://prove2.me/submissions/f8bb1e05-a83c-408d-8a13-81c8da7b6bb3

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_ValuationMultiplicationInvariance
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_QuadTie
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_GenCalc

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory
  CartesianMonoidalCategory MonObj
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.GC
open ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi IsLocalRing
variable {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] {ϖ : V}
  {F : Type} [Field F] [Algebra (FractionRing V) F] {v : AddValuation F (WithTop ℚ)}
namespace ReciprocityTheory.ChartRestriction.G.DVR.GC
theorem _root_.solution (hϖ : Irreducible ϖ) (hv : ValOver ϖ F v) (c : V) :
    (0 : WithTop ℚ) ≤ v (algebraMap (FractionRing V) F (algebraMap V (FractionRing V) c)) := by
  by_cases hc : c = 0
  · simp [hc]
  obtain ⟨n, u, hu⟩ := IsDiscreteValuationRing.associated_pow_irreducible hc hϖ
  have hval : HasVal ϖ (algebraMap V (FractionRing V) c) (n : ℤ) := ⟨u⁻¹, by
    rw [zpow_natCast, ← map_pow, ← map_mul]; congr 1
    rw [← hu, _root_.mul_assoc, Units.mul_inv, _root_.mul_one]⟩
  rw [hv _ _ hval]
  exact WithTop.coe_nonneg.2 (by positivity)
end ReciprocityTheory.ChartRestriction.G.DVR.GC
