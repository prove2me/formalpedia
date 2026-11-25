-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Chart.scaleS_comp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T15:12:22.940814+00:00
-- url     : https://prove2.me/submissions/73fd1b01-8b8f-4393-a174-3fe1064b2163

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
variable {S : Type} [CommRing S]
namespace ReciprocityTheory.ChartRestriction.G.Chart
theorem _root_.solution {A : Type} [CommRing A] [Algebra S A] (a b : A) :
    (scaleS (S := S) a).comp (scaleS b) = scaleS (a * b) := by
  refine AlgHom.ext fun x => TrivSqZeroExt.ext ?_ ?_ <;> simp [scaleS] <;> ring
end ReciprocityTheory.ChartRestriction.G.Chart
