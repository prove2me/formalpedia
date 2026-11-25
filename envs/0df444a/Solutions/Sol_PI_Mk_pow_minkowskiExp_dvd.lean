-- Prove2me | solution 1 for PI.Mk.pow_minkowskiExp_dvd
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T09:58:24.167185+00:00
-- url     : https://prove2.me/submissions/57057dc6-78d9-4c0b-af79-2699c570b02d

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_Minkowski
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MinkowskiBound_PowerSumStep
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MinkowskiBound_Assemble
import Theorems.Thm_PI_Mk_minkowskiExp_eq_zero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PI PI.Mk
open Finset
namespace PI.Mk
theorem _root_.solution (N ℓ : ℕ) (hℓ : ℓ.Prime) :
    ℓ ^ PI.minkowskiExp N ℓ ∣ PI.minkowskiM N := by
  by_cases h : ℓ < N + 2
  · unfold PI.minkowskiM
    exact Finset.dvd_prod_of_mem (fun p => p ^ PI.minkowskiExp N p)
      (Finset.mem_filter.2 ⟨Finset.mem_range.2 h, hℓ⟩)
  · rw [minkowskiExp_eq_zero N ℓ (by omega), pow_zero]
    exact one_dvd _
end PI.Mk
