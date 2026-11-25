-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.T0.LocAt.intAt_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T16:00:26.762406+00:00
-- url     : https://prove2.me/submissions/a5b1adc5-82c3-4dc4-907c-133348b9e23b

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_DiscLocal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_HDiscBDefs
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_HDiscAF
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_NormFactorizationClause
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_NormByPlaces
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_UnitAtIntAt

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option linter.style.haveILetI false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.T0
open NumberField
open ReciprocityTheory.ChartRestriction.G.T0.LocAt
variable {R F : Type*} [CommRing R] [IsDomain R] [Field F] [Algebra R F] [IsFractionRing R F]
variable {p : Ideal R} [hP : p.IsPrime]
include hP
omit [IsDomain R] [IsFractionRing R F]
namespace ReciprocityTheory.ChartRestriction.G.T0.LocAt
theorem _root_.solution {x y : F} (hx : IntAt p x) (hy : IntAt p y) : IntAt p (x * y) := by
  obtain ⟨a, s, hs, hxs⟩ := hx
  obtain ⟨b, t, ht, hyt⟩ := hy
  refine ⟨a * b, s * t, fun h => (hP.mem_or_mem h).elim hs ht, ?_⟩
  rw [map_mul, map_mul, ← hxs, ← hyt]
  ring
end ReciprocityTheory.ChartRestriction.G.T0.LocAt
