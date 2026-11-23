-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.DVR.uVal_tr
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T12:29:17.092972+00:00
-- url     : https://prove2.me/submissions/07c05af1-32f3-462b-9943-65419d4f7c0d

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_PhiGen
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_PhiGenPf
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_tr_fst
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_tr_pr

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
theorem _root_.solution (α : D.X) (m m' : TF (R := R) F ⟶ D.P.A) (y : (DegPre.BF D F).left) (J) :
    uVal D F k α m (DegPre.trPt D F m') y J =
      cubN (th D y J) k (cP D _ α) (fst _ _ ≫ m) (DegPre.prB D F * (fst _ _ ≫ m')) *
        (th D y J (cP D _ α) (DegPre.prB D F * (fst _ _ ≫ m')) (fst _ _ ≫ m))⁻¹ := by
  simp only [uVal]
  rw [← Category.assoc, tr_fst, tr_pr]
end ReciprocityTheory.ChartRestriction.G.DVR
