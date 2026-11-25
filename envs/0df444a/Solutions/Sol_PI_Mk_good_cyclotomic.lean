-- Prove2me | solution 1 for PI.Mk.good_cyclotomic
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T10:05:35.609587+00:00
-- url     : https://prove2.me/submissions/daafbaaa-851a-4790-8d74-a48b4271b96a

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MinkowskiBound_PowerSumStep
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MinkowskiBound_CharpolyDvdOfPowEqOne
import Theorems.Thm_PI_Mk_good_cyclotomic_one
import Theorems.Thm_PI_Mk_good_cyclotomic_succ

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PI PI.Mk
open Polynomial Matrix
namespace PI.Mk
theorem _root_.solution (ℓ : ℕ) (hℓ : ℓ.Prime) (j : ℕ) : Good ℓ (cyclotomic (ℓ ^ j) ℚ) := by
  rcases j with _ | j
  · rw [pow_zero]; exact good_cyclotomic_one ℓ
  · exact good_cyclotomic_succ ℓ hℓ j
end PI.Mk
