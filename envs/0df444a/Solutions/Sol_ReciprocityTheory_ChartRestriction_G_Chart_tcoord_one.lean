-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Chart.tcoord_one
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:14:25.771173+00:00
-- url     : https://prove2.me/submissions/29d7692a-be4d-446b-b479-d8b1b3d72ea6

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_UniversalCharts_DualLiftInjective
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_UniversalCharts_RestrictDiagCompInclFst
import Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_Chart_comp_one__39cc6a6ed057
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_jetAug_zR
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_jet_ext
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_spMap_comp
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_spMap_jetAug_alt
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_tcoord_eq


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
theorem _root_.solution : tcoord hx (1 : sp (R₀ := R) (DualNumber R) ⟶ G) isTan_one = 0 := by
  apply tcoord_eq
  have : dualLift (R := R) (0 : Fin n → R) = (Algebra.ofId R (DualNumber R)).comp (jetAug R (Fin n) 1) :=
    jet_ext fun j => by
      rw [dualLift_zR, AlgHom.comp_apply, jetAug_zR, map_zero, Pi.zero_apply, TrivSqZeroExt.inr_zero]
  rw [this, ← spMap_comp, Category.assoc, spMap_jetAug_alt hx, comp_one']
end ReciprocityTheory.ChartRestriction.G.Chart
