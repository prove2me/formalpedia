-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.DVR.gt_mul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:29:38.181581+00:00
-- url     : https://prove2.me/submissions/a1a773f6-9238-41b9-879b-3b5d6a8a5232

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_PhiGen
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_PhiGenPf
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_comp_cP
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_val_corr
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_val_cub


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
variable {D F} {T : Over (Spec (CommRingCat.of R))} (σ : T ⟶ TF (R := R) F) {z : T.left}
  {J : (T.left ⟶ D.P.A.left) → D.P.L.ι} (hJ : Good D.P.L z J)
include hJ
namespace ReciprocityTheory.ChartRestriction.G.DVR
theorem _root_.solution (g : GtPtF D F) (a a' : D.X) :
    val (g.s (a + a')) σ.left z J * th D z J (cP D T a) (cP D T a') (σ ≫ g.b) =
      val (g.s a) σ.left z J * val (g.s a') σ.left z J := by
  have := (val_mul hJ _ _ _).symm.trans ((val_corr hJ (g.mult a a') σ.left).trans (val_mul hJ _ _ _))
  refine Eq.trans (congrArg₂ (· * ·) rfl ?_) this
  refine Eq.trans ?_ (val_cub D.cub σ hJ (cP D _ a) (cP D _ a') g.b).symm
  rw [comp_cP, comp_cP]
end ReciprocityTheory.ChartRestriction.G.DVR
