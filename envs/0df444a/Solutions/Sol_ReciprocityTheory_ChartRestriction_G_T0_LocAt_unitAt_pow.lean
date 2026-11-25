-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.T0.LocAt.unitAt_pow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T16:30:13.661003+00:00
-- url     : https://prove2.me/submissions/1f35de62-7cc6-4674-a3de-8994c55b5928

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_DiscLocal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_HDiscBDefs
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_HDiscAF
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_NormFactorizationClause
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_NormByPlaces
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_UnitAtIntAt
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_LocAt_unitAt_mul
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_LocAt_unitAt_one

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
theorem _root_.solution {x : F} (hx : UnitAt p x) (n : ℕ) : UnitAt p (x ^ n) := by
  induction n with
  | zero => rw [pow_zero]; exact unitAt_one
  | succ n ih => rw [pow_succ]; exact unitAt_mul ih hx
end ReciprocityTheory.ChartRestriction.G.T0.LocAt
