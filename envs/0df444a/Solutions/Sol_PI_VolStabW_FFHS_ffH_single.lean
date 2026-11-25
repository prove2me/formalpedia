-- Prove2me | solution 1 for PI.VolStabW.FFHS.ffH_single
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T10:58:32.556977+00:00
-- url     : https://prove2.me/submissions/5cb9db5b-1711-4f20-9f55-4f3ca2cbb5a9

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_LocDensFFCnt
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_LocDensFFIn

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.VolStabW PI.VolStabW.FFHS
open Module Polynomial
variable {K : Type} [Field K] {σ : K →+* K}
namespace PI.VolStabW.FFHS
theorem _root_.solution {n : ℕ} (T : Matrix (Fin n) (Fin n) K) (i j : Fin n) :
    ffH σ T (Pi.single i 1) (Pi.single j 1) = T i j := by
  simp [ffH, Pi.single_apply, apply_ite σ]
end PI.VolStabW.FFHS
