-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.DVR.smul_star_inj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T14:10:59.31438+00:00
-- url     : https://prove2.me/submissions/71e7c094-37bf-4d51-8a4d-9ee57c2953e7

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_CartesianLiftThreeCompProjection
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_LBCorr
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_ValuationMultiplicationInvariance
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_PullGen

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
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.DVR
open ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi IsLocalRing
variable {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
  (D : DegData V (maximalIdeal V)) (F : Type) [Field F] [Algebra (FractionRing V) F]
  {O : Type} [CommRing O] [StarRing O] [Module O D.toPre.X]
namespace ReciprocityTheory.ChartRestriction.G.DVR
theorem _root_.solution {O : Type} [CommRing O] [StarRing O] {X : Type} [AddCommGroup X] [Module O X]
    [Module.Free ℤ X] (a : O) (N : ℕ) (hN : a * star a = (N : O)) (hN1 : 1 ≤ N) {χ₁ χ₂ : X}
    (h : star a • χ₁ = star a • χ₂) : χ₁ = χ₂ := by
  have h2 : (a * star a) • χ₁ = (a * star a) • χ₂ := by rw [mul_smul, mul_smul, h]
  rw [hN, Nat.cast_smul_eq_nsmul, Nat.cast_smul_eq_nsmul] at h2
  have h3 : (N : ℤ) • χ₁ = (N : ℤ) • χ₂ := by rw [natCast_zsmul, natCast_zsmul]; exact h2
  exact smul_right_injective X (by omega) h3
end ReciprocityTheory.ChartRestriction.G.DVR
