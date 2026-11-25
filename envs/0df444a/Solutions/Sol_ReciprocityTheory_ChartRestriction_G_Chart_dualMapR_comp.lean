-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Chart.dualMapR_comp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T15:33:12.966958+00:00
-- url     : https://prove2.me/submissions/dbd6573b-96c0-4147-a382-672f19beee3a

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_DualMapSOfIdToRingHom
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_DualMapSCompScaleS
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsGrpPullback_comp


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
open scoped CategoryTheory.Obj
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Chart
attribute [local instance] Over.cartesianMonoidalCategory
variable {S : Type} [CommRing S] {G : Over (Spec (CommRingCat.of S))} [GrpObj G]
namespace ReciprocityTheory.ChartRestriction.G.Chart
theorem _root_.solution {A A' A'' : Type} [CommRing A] [CommRing A'] [CommRing A''] (f : A →+* A') (g : A' →+* A'') :
    dualMapR (g.comp f) = (dualMapR g).comp (dualMapR f) := by
  refine RingHom.ext fun a => TrivSqZeroExt.ext ?_ ?_ <;> simp [dualMapR]
end ReciprocityTheory.ChartRestriction.G.Chart
