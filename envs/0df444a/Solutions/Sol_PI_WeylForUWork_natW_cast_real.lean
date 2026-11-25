-- Prove2me | solution 1 for PI.WeylForUWork.natW_cast_real
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T11:53:24.038827+00:00
-- url     : https://prove2.me/submissions/e4aa22b1-e66b-433d-a628-7fc397f664f5

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_WeylForU
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeylFormulaUnitary_NatWCastReal
import Theorems.Thm_PI_WeylForUWork_natW_cast

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.WeylForUWork
open Finset PI.UpqRep Formalism.BasicNotions
namespace PI.WeylForUWork
theorem _root_.solution {N : ℕ} (lam : DomWeight N) (i : Fin N) :
    ((lam.natW i : ℕ) : ℝ) = ((lam.w i : ℤ) : ℝ) - ((lam.detShift : ℤ) : ℝ) := by
  exact_mod_cast natW_cast lam i
end PI.WeylForUWork
