-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.T0.LocAt.unitAt_inv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T16:08:03.209896+00:00
-- url     : https://prove2.me/submissions/fcd6058a-c8f2-4e6b-95fc-c25fbaf4481e

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
namespace ReciprocityTheory.ChartRestriction.G.T0.LocAt
theorem _root_.solution {x : F} (hx : UnitAt p x) : UnitAt p x⁻¹ := by
  obtain ⟨a, s, ha, hs, h⟩ := hx
  refine ⟨s, a, hs, ha, ?_⟩
  have ha0 : algebraMap R F a ≠ 0 := by
    intro h0
    apply ha
    have h00 : a = 0 := IsFractionRing.injective R F (by rw [h0, map_zero])
    rw [h00]
    exact p.zero_mem
  have hx0 : x ≠ 0 := by
    rintro rfl
    apply ha0
    rw [← h, zero_mul]
  rw [← h, ← mul_assoc, inv_mul_cancel₀ hx0, one_mul]
end ReciprocityTheory.ChartRestriction.G.T0.LocAt
