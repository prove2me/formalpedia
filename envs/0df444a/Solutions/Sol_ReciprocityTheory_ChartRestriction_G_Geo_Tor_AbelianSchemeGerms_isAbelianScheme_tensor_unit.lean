-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Geo.Tor.AbelianSchemeGerms.isAbelianScheme_tensor_unit
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T13:25:22.692633+00:00
-- url     : https://prove2.me/submissions/f0344ac7-d194-49ab-a3e1-87545f4ffb86

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
theorem _root_.solution (G : Over S) [GrpObj G] (hG : IsAbelianScheme G) :
    IsAbelianScheme (G ⊗ 𝟙_ (Over S)) := by
  have := hG.comm
  have := hG.smooth
  have := hG.proper
  have := hG.geomConnected
  have hc : (G ⊗ 𝟙_ (Over S)).hom = pullback.snd G.hom (𝟙_ (Over S)).hom := by
    rw [Over.tensorObj_hom, pullback.condition]
    exact Category.comp_id _
  refine ⟨inferInstance, ?_, ?_, ?_⟩
  · rw [hc]; infer_instance
  · rw [hc]; infer_instance
  · rw [hc]; infer_instance
end ReciprocityTheory.ChartRestriction.G.Geo.Tor.AbelianSchemeGerms
