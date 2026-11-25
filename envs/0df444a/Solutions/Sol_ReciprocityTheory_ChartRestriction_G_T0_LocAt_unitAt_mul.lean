-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.T0.LocAt.unitAt_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T15:56:06.452602+00:00
-- url     : https://prove2.me/submissions/5fc83668-fd81-4450-b495-7287b7475cbe

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
theorem _root_.solution {x y : F} (hx : UnitAt p x) (hy : UnitAt p y) : UnitAt p (x * y) := by
  obtain ⟨a, s, ha, hs, hxs⟩ := hx
  obtain ⟨b, t, hb, ht, hyt⟩ := hy
  refine ⟨a * b, s * t, fun h => (hP.mem_or_mem h).elim ha hb,
    fun h => (hP.mem_or_mem h).elim hs ht, ?_⟩
  rw [map_mul, map_mul, ← hxs, ← hyt]
  ring
end ReciprocityTheory.ChartRestriction.G.T0.LocAt
