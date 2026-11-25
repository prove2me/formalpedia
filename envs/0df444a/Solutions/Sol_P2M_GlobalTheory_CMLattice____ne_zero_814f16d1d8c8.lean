-- Prove2me | solution 1 for P2M_GlobalTheory_CMLattice____ne_zero_814f16d1d8c8
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T01:50:31.316439+00:00
-- url     : https://prove2.me/submissions/763dd7c8-cad7-4abc-9123-71170ac239df

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_LatticeCmEqIdealAndCovolume

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex NumberField Module
open scoped nonZeroDivisors
open GlobalTheory
open GlobalTheory.CMLattice
variable {K : Type} [Field K] [NumberField K]
namespace GlobalTheory.CMLattice
theorem _root_.solution (L : PeriodPair) : L.ω₁ ≠ 0 := by
  simpa using L.indep.ne_zero 0
end GlobalTheory.CMLattice
