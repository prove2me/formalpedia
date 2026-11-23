-- Prove2me | solution 1 for P2M_GlobalTheory_PeriodChart_star_mulVec__98f0c4b56c3f
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:20:53.206802+00:00
-- url     : https://prove2.me/submissions/6b3b6320-0b3e-4459-ad5f-3fdb75ad4d4a

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_ExistsContraction

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Matrix Module
open ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.PeriodChart
variable {g : ℕ}
namespace GlobalTheory.PeriodChart
theorem _root_.solution (B : Matrix (Fin g) (Fin g) ℂ) (w : Fin g → ℂ) :
    star (B *ᵥ w) = B.map (starRingEnd ℂ) *ᵥ star w := by
  funext i
  simp only [Pi.star_apply, mulVec, dotProduct, Matrix.map_apply, star_sum, star_mul', Complex.star_def]
end GlobalTheory.PeriodChart
