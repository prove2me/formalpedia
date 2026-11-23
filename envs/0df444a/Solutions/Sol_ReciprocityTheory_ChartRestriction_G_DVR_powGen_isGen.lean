-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.DVR.powGen_isGen
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:34:16.364938+00:00
-- url     : https://prove2.me/submissions/17dda1ff-e306-49d1-a3df-83ebe68de564

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_PhiGen
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_PhiGenPf

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
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
variable {R : Type} [CommRing R] [IsDomain R] (D : DegPre R) (F : Type) [Field F] [Algebra (FractionRing R) F]
namespace ReciprocityTheory.ChartRestriction.G.DVR
theorem _root_.solution {X Y : Scheme.{0}} (L : LB X) {K : Type} [Fintype K] (φ : K → (Y ⟶ X)) (ε : K → ℤ)
    (t : LB.Gen (LB.LinComb L φ ε)) (ht : t.IsGen) (n : ℕ) : (GeneratorPullback.powGen L φ ε t n).IsGen := fun i j => by
  refine ((map_pow _ _ _).trans ((congrArg (· ^ n) (ht i j)).trans (mul_pow _ _ _))).trans
    (congrArg₂ (· * ·) ?_ (map_pow _ _ _).symm)
  exact (Finset.prod_pow _ _ _).symm.trans (Finset.prod_congr rfl fun k _ =>
    (zpow_natCast _ n).symm.trans ((zpow_mul _ _ _).symm.trans (congrArg _ (mul_comm _ _))))
end ReciprocityTheory.ChartRestriction.G.DVR
