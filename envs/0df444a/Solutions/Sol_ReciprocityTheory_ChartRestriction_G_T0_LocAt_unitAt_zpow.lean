-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.T0.LocAt.unitAt_zpow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T16:46:27.552492+00:00
-- url     : https://prove2.me/submissions/f2e1afdf-7a9d-42b6-87c3-8c923c7ac7af

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_DiscLocal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_HDiscBDefs
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_HDiscAF
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_NormFactorizationClause
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_NormByPlaces
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_UnitAtIntAt
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_LocAt_unitAt_inv
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_LocAt_unitAt_pow

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
theorem _root_.solution {x : F} (hx : UnitAt p x) (n : ℤ) : UnitAt p (x ^ n) := by
  cases n with
  | ofNat n =>
    show UnitAt p (x ^ (n : ℤ))
    rw [zpow_natCast]
    exact unitAt_pow hx n
  | negSucc n =>
    rw [zpow_negSucc]
    exact unitAt_inv (unitAt_pow hx (n + 1))
end ReciprocityTheory.ChartRestriction.G.T0.LocAt
