-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Chart.pt_eps
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:14:24.665888+00:00
-- url     : https://prove2.me/submissions/d2b46b21-2877-475f-bc94-e9d7fda6d16c

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_UniversalCharts_LePreimageOfNil
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_pt_left

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
variable {R₀ : Type} [CommRing R₀]
variable {G : Over (Spec (CommRingCat.of R₀))} [GrpObj G]
namespace ReciprocityTheory.ChartRestriction.G.Chart
theorem _root_.solution (C : Chart G) (P : Type) [CommRing P] [Algebra R₀ P] :
    pt C ((Algebra.ofId R₀ P).comp (eps C)) = (1 : sp P ⟶ G) := by
  apply Over.OverMorphism.ext
  rw [pt_left]
  have e : CommRingCat.ofHom ((Algebra.ofId R₀ P).comp (eps C)).toRingHom =
      epsHom C ≫ CommRingCat.ofHom (algebraMap R₀ P) := rfl
  rw [e, Spec.map_comp, Category.assoc, epsHom_spec]
  first
  | rfl
  | (rw [MonObj.Hom.one_def]; rfl)
  | simp [MonObj.Hom.one_def]
end ReciprocityTheory.ChartRestriction.G.Chart
