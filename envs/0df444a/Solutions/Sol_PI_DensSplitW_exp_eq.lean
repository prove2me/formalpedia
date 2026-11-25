-- Prove2me | solution 1 for PI.DensSplitW.exp_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T09:35:21.428003+00:00
-- url     : https://prove2.me/submissions/b6d836e4-1b61-4553-9f35-04897d7bcecf

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_SiegelMassRatios_DensExact
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SplitDensity_FiberCard
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SplitDensity_PhiXFinrankRange

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset Formalism.L2.SG.DensExact
open PI PI.DensSplitW
namespace PI.DensSplitW
theorem _root_.solution (n m r : ℕ) (hmn : m ≤ n) (hrm : r ≤ m) :
    n * m + r * (n - m) + (n - m) * (m - r) = 2 * n * m - m ^ 2 := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hmn
  obtain ⟨e, rfl⟩ := Nat.exists_eq_add_of_le hrm
  rw [Nat.add_sub_cancel_left, Nat.add_sub_cancel_left]
  apply (Nat.sub_eq_of_eq_add _).symm
  ring
end PI.DensSplitW
