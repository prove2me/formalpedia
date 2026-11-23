-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Chart.tcoord_scale
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:54:16.441389+00:00
-- url     : https://prove2.me/submissions/1a176c26-c931-488f-9593-ee5f39e4050a

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_UniversalCharts_DualLiftInjective
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_UniversalCharts_RestrictDiagCompInclFst
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_jet_ext
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_spMap_comp
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_tcoord_eq
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_tcoord_spec


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
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Chart
attribute [local instance] Over.cartesianMonoidalCategory
variable {R : Type} [CommRing R]
variable {G : Over (Spec (CommRingCat.of R))} [GrpObj G]
variable {n : ℕ} {x : ∀ m : ℕ, sp (R₀ := R) (JetR R (Fin n) m) ⟶ G} (hx : IsUnivChart G n x)
namespace ReciprocityTheory.ChartRestriction.G.Chart
theorem _root_.solution (c : R) {w : sp (R₀ := R) (DualNumber R) ⟶ G} (h : IsTan w) :
    tcoord hx (spMap (scaleD c) ≫ w) (isTan_scale c h) = c • tcoord hx w h := by
  apply tcoord_eq
  conv_lhs => rw [tcoord_spec hx w h]
  rw [← Category.assoc, spMap_comp]
  congr 2
  apply jet_ext
  intro j
  rw [AlgHom.comp_apply, dualLift_zR, dualLift_zR, TrivSqZeroExt.map_inr, LinearMap.smul_apply,
    LinearMap.id_apply, Pi.smul_apply]
end ReciprocityTheory.ChartRestriction.G.Chart
