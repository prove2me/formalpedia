-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.DVR.TWM.appTop_specMap
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:35:56.564521+00:00
-- url     : https://prove2.me/submissions/92a6da0a-6890-433d-9902-1a8e8b85c0d9

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_ExistsWeightBasisFiltration
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_TwistBC
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_SectionScalarValuation
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_GenCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_TWMove

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
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.TWM
open ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor IsLocalRing TWO SectionScalarValuation
namespace ReciprocityTheory.ChartRestriction.G.DVR.TWM
theorem _root_.solution {R S : CommRingCat} (g : R ⟶ S) (r : Γ(Spec R, ⊤)) :
    (Spec.map g).appTop.hom r = (Scheme.ΓSpecIso S).inv.hom (g.hom ((Scheme.ΓSpecIso R).hom.hom r)) := by
  have e := congrArg (fun φ => φ.hom r) (Scheme.ΓSpecIso_naturality g)
  simp only [CommRingCat.hom_comp, RingHom.comp_apply] at e
  rw [← e]
  simp
end ReciprocityTheory.ChartRestriction.G.DVR.TWM
