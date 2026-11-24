-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.DVR.TG.app_injective_of_flat_surj
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:13:58.959657+00:00
-- url     : https://prove2.me/submissions/cd1543de-6703-41a3-8745-b3f59efdfc12

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_ThetaGenFlat

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.TG
noncomputable section
set_option backward.isDefEq.respectTransparency.types false
namespace ReciprocityTheory.ChartRestriction.G.DVR.TG
theorem _root_.solution {Y Z : Scheme.{0}} (q : Y ⟶ Z) [Flat q] [Surjective q] (V : Z.Opens) :
    Function.Injective (q.app V) := by
  intro a b hab
  refine TopCat.Presheaf.section_ext Z.sheaf V a b fun z hz => ?_
  obtain ⟨y, rfl⟩ := q.surjective z
  have hinj : Function.Injective (q.stalkMap y) := by
    algebraize [(q.stalkMap y).hom]
    have : Module.FaithfullyFlat (Z.presheaf.stalk (q y)) (Y.presheaf.stalk y) :=
      @Module.FaithfullyFlat.of_flat_of_isLocalHom _ _ _ _ _ _ _
        (Flat.stalkMap q y) (q.toLRSHom.prop y)
    exact ‹RingHom.FaithfullyFlat _›.injective
  apply hinj
  show q.stalkMap y (Z.presheaf.germ V (q y) hz a) = q.stalkMap y (Z.presheaf.germ V (q y) hz b)
  rw [Scheme.Hom.germ_stalkMap_apply, Scheme.Hom.germ_stalkMap_apply, hab]
end ReciprocityTheory.ChartRestriction.G.DVR.TG
