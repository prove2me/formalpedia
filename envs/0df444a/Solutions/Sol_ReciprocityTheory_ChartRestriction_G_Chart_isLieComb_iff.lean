-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Chart.isLieComb_iff
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:44:09.338159+00:00
-- url     : https://prove2.me/submissions/740753f6-f5ea-4962-a871-044c37ff44b7

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_UniversalCharts_DualLiftCompJetSub
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_UniversalCharts_UnivChartLoc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsLieBasis
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_UniversalCharts_ChartLaw

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
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp epsR epsScaleR IsTangent IsLieComb IsLieBasis)
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Chart
attribute [local instance] Over.cartesianMonoidalCategory
variable {R : Type} [CommRing R]
variable {G : Over (Spec (CommRingCat.of R))} [GrpObj G]
namespace ReciprocityTheory.ChartRestriction.G.Chart
theorem _root_.solution {d : ℕ} (c : Fin d → R) (v : Fin d → (epsR R ⟶ G)) (w : epsR R ⟶ G) :
    IsLieComb c v w ↔ w = prodPts c v := by
  constructor
  · rintro ⟨u, hu, rfl⟩
    have : u = fun i => spMap (scaleD (c i)) ≫ v i := by
      funext i
      apply Over.OverMorphism.ext
      rw [hu i]
      rfl
    rw [this]
    rfl
  · intro h
    exact ⟨fun i => spMap (scaleD (c i)) ≫ v i, fun i => rfl, h⟩
end ReciprocityTheory.ChartRestriction.G.Chart
