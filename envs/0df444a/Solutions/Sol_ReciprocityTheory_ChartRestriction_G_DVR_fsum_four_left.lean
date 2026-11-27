-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.DVR.fsum_four_left
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-27T05:30:31.943303+00:00
-- url     : https://prove2.me/submissions/f562884e-eb9f-4083-b3a1-aaf557b80a5a

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
theorem _root_.solution {S' : Scheme.{0}} {T A : Over S'} [GrpObj A] [IsCommMonObj A] (x₀ x₁ x₂ x₃ : T ⟶ A) (e : Fin 4 → ℤ) :
    fsum ![x₀.left, x₁.left, x₂.left, x₃.left] e =
      lf (e 0 • Finsupp.single x₀ 1 + e 1 • Finsupp.single x₁ 1 + e 2 • Finsupp.single x₂ 1 +
        e 3 • Finsupp.single x₃ 1) := by
  simp [fsum, lf, Fin.sum_univ_four, Finsupp.mapDomain_add, Finsupp.mapDomain_smul, Finsupp.smul_single]
end ReciprocityTheory.ChartRestriction.G.DVR
