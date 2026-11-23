-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.DVR.pullU_comp
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:17:25.909884+00:00
-- url     : https://prove2.me/submissions/03b4d789-4e2e-4f1b-bedd-13dfe1e8c65f

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_LBLocal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_LBPull

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
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.DVR
open ReciprocityTheory.ChartRestriction.G.Semi
namespace ReciprocityTheory.ChartRestriction.G.DVR
theorem _root_.solution {X Y Z : Scheme.{0}} (f : Z ⟶ Y) (g : Y ⟶ X) (U : X.Opens) (x : Γ(X, U)ˣ) :
    pullU (f ≫ g) U x = pullU f (g ⁻¹ᵁ U) (pullU g U x) := by
  ext
  simp only [pullU, Units.coe_map, MonoidHom.coe_coe, Scheme.Hom.comp_app]
  rfl
end ReciprocityTheory.ChartRestriction.G.DVR
