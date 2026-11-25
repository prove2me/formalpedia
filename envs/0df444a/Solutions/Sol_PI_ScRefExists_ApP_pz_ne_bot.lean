-- Prove2me | solution 1 for PI.ScRefExists.ApP.pz_ne_bot
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T10:30:01.858925+00:00
-- url     : https://prove2.me/submissions/0864d866-89d6-4bc8-8f55-9b042e357de9

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeReferenceFrame_PPAssemble
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeReferenceFrame_PrincipalIdealRingAtPrime

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField Formalism.MainNotions.S IsDedekindDomain
open scoped TensorProduct nonZeroDivisors
open PI PI.ScRefExists PI.ScRefExists.ApP
open PI.ScRefExists.Sk
namespace PI.ScRefExists.ApP
theorem _root_.solution {p : ℕ} (hp : p.Prime) : Pz p ≠ ⊥ := by
  rw [Ne, Ideal.span_singleton_eq_bot]
  exact_mod_cast hp.ne_zero
end PI.ScRefExists.ApP
