-- Prove2me | solution 2 for PI.WFJM.Shape.natFloor_of_int
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:24:47.060508+00:00
-- url     : https://prove2.me/submissions/2364cc9a-5582-4298-afce-d5fa466b1192

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockJointMultiplicity_GlobalTheory
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockJointMultiplicity_ShapeFromFacts

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix FockH1Action
open PI PI.WFJM PI.WFJM.Shape
open PI.FJM
variable {n : ℕ}
namespace PI.WFJM.Shape
theorem _root_.solution (x : ℚ) (z : ℤ) (hz : (z : ℚ) = x) (hx : 0 ≤ x) : ((⌊x⌋₊ : ℕ) : ℚ) = x := by
  have hz0 : 0 ≤ z := by
    have : (0 : ℚ) ≤ z := by rw [hz]; exact hx
    exact_mod_cast this
  obtain ⟨k, rfl⟩ := Int.eq_ofNat_of_zero_le hz0
  rw [← hz]
  push_cast
  rw [Nat.floor_natCast]
end PI.WFJM.Shape
