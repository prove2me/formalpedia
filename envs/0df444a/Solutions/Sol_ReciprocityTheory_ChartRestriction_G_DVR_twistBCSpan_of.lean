-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.DVR.twistBCSpan_of
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T16:55:46.59469+00:00
-- url     : https://prove2.me/submissions/c0b103ab-6f32-4b4c-b9f9-7a170c5b4203

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_TwistBC
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_AppCompatGeneric
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_TwistBCPf

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
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.DVR
open ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
namespace ReciprocityTheory.ChartRestriction.G.DVR
theorem _root_.solution (h : TwistBaseChangeStatement) : TwistBCSpanStatement := by
  intro R _ _ _ _ D k hk α R' _ _ f _ s'
  obtain ⟨m, b, -, hb⟩ := h R D k hk α
  have hbasis := hb R' f (fun i => pullSec D.P.L (DegPre.famφB D α) (DegPre.famε k) (b i)
      (snd (Over.mk (Spec.map (CommRingCat.ofHom f))) D.P.A).left) (fun i j => rfl)
  obtain ⟨r, hr, -⟩ := hbasis s'
  exact ⟨m, r, b, hr⟩
end ReciprocityTheory.ChartRestriction.G.DVR
