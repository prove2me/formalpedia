-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.DVR.uVal_id
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:17:33.53435+00:00
-- url     : https://prove2.me/submissions/c103bfd4-4bec-4777-9ac5-3a5c5185c834

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
variable {D F}
variable (hG : GlobalFnsSt) {k : ℕ} (p : QkPt D F k)
  (w : LB.Gen (LB.LinComb D.P.L (DegPre.lineφ D F p.g.b) (DegPre.lineε k))) (hw : w.IsGen)
include hG hw
omit hG hw
namespace ReciprocityTheory.ChartRestriction.G.DVR
theorem _root_.solution (α : D.X) (m : TF (R := R) F ⟶ D.P.A) (y : (DegPre.BF D F).left) (J) :
    uVal D F k α m (𝟙 _) y J = cubN (th D y J) k (cP D _ α) (fst _ _ ≫ m) (DegPre.prB D F) *
      (th D y J (cP D _ α) (DegPre.prB D F) (fst _ _ ≫ m))⁻¹ := by
  simp only [uVal, Category.id_comp]
end ReciprocityTheory.ChartRestriction.G.DVR
