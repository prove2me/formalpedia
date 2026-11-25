-- Prove2me | solution 1 for PI.KLW.NO.rp_two
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T09:54:48.136457+00:00
-- url     : https://prove2.me/submissions/a6d1a717-721c-43f1-a3ea-1fecc2f527a7

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalLatticeIsomorphism_NormOneB
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalLatticeIsomorphism_NormOneC
import Theorems.Thm_PI_KLW_Rp_natCast


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open NumberField
open PI PI.KLW PI.KLW.NO
namespace PI.KLW.NO
theorem _root_.solution {K : Type} [Field K] [NumberField K] {p : ℕ} : Rp K p (2 : K) := by
  simpa using Rp_natCast (K := K) (p := p) 2
end PI.KLW.NO
