-- Prove2me | solution 1 for PI.VolStabS.FiniteFieldCounting.exp_id
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T10:50:56.181173+00:00
-- url     : https://prove2.me/submissions/d30c6627-d5b7-4c18-8578-98f0935c6faa

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerVolume_LocDensFFS
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerVolume_LocDensFFT

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.VolStabS
open PI.VolStabS.FiniteFieldCounting
namespace PI.VolStabS.FiniteFieldCounting
theorem _root_.solution (M a : ℕ) (ha : a ≤ M) : M * a + a * (M - a) = 2 * M * a - a ^ 2 := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le ha
  rw [Nat.add_sub_cancel_left]
  symm
  apply Nat.sub_eq_of_eq_add
  ring
end PI.VolStabS.FiniteFieldCounting
