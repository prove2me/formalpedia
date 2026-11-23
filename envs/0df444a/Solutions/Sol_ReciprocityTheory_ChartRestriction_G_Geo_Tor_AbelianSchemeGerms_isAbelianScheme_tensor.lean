-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Geo.Tor.AbelianSchemeGerms.isAbelianScheme_tensor
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:18:05.111113+00:00
-- url     : https://prove2.me/submissions/35fab467-6feb-48ed-b279-c28676039b11

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_DegProd
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_AbelianSchemeGerms

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
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.AbelianSchemeGerms
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
variable {S : Scheme.{0}}
namespace ReciprocityTheory.ChartRestriction.G.Geo.Tor.AbelianSchemeGerms
theorem _root_.solution (G H : Over S) [GrpObj G] [GrpObj H] (hG : IsAbelianScheme G)
    (hH : IsAbelianScheme H) : IsAbelianScheme (G ⊗ H) := by
  have := hG.comm
  have := hH.comm
  have := hG.smooth
  have := hH.smooth
  have := hG.proper
  have := hH.proper
  have := hG.geomConnected
  have := hH.geomConnected
  refine ⟨inferInstance, ?_, ?_, ?_⟩
  · rw [Over.tensorObj_hom, pullback.condition]
    infer_instance
  · rw [Over.tensorObj_hom, pullback.condition]
    infer_instance
  · rw [Over.tensorObj_hom, pullback.condition]
    exact GeometricallyConnected.comp _ _
end ReciprocityTheory.ChartRestriction.G.Geo.Tor.AbelianSchemeGerms
