-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Chart.isTan_iff
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:43:33.640115+00:00
-- url     : https://prove2.me/submissions/cec310cc-6b25-410b-bb3c-4a1ab704fe4e

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_UniversalCharts_DualLiftCompJetSub
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_UniversalCharts_UnivChartLoc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsLieBasis
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_UniversalCharts_ChartLaw
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_spMap_left


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
theorem _root_.solution (w : sp (R₀ := R) (DualNumber R) ⟶ G) : IsTan w ↔ IsTangent w := by
  constructor
  · intro h
    have := congrArg CommaMorphism.left h
    simp only [Over.comp_left, spMap_left] at this
    show Spec.map _ ≫ w.left = _
    rw [this]
    show (sp R).hom ≫ η[G].left = η[G].left
    simp only [Over.mk_hom]
    rw [Algebra.algebraMap_self, CommRingCat.ofHom_id, Spec.map_id]
    exact Category.id_comp _
  · intro h
    apply Over.OverMorphism.ext
    simp only [Over.comp_left, spMap_left]
    refine h.trans ?_
    show η[G].left = (sp R).hom ≫ η[G].left
    simp only [Over.mk_hom]
    rw [Algebra.algebraMap_self, CommRingCat.ofHom_id, Spec.map_id]
    exact (Category.id_comp _).symm
end ReciprocityTheory.ChartRestriction.G.Chart
