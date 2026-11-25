-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Chart.toAlgHom_restrict
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T15:24:36.0198+00:00
-- url     : https://prove2.me/submissions/ed690026-2401-43eb-8215-d94f3f09eed2

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_DualMapSOfIdToRingHom
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_DualMapSCompScaleS

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
namespace ReciprocityTheory.ChartRestriction.G.Chart
theorem _root_.solution {S : Type} [CommRing S] (R : Type) [CommRing R] [Algebra S R] (A A' : Type) [CommRing A]
    [Algebra S A] [Algebra R A] [IsScalarTower S R A] [CommRing A'] [Algebra S A'] [Algebra R A'] [IsScalarTower S R A']
    [Algebra A A'] [IsScalarTower R A A'] [IsScalarTower S A A'] :
    (IsScalarTower.toAlgHom R A A').restrictScalars S = IsScalarTower.toAlgHom S A A' := AlgHom.ext fun _ => rfl
end ReciprocityTheory.ChartRestriction.G.Chart
