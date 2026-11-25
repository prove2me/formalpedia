-- Prove2me | solution 1 for PI.ScRefExists.ApP.principal_ideal_ring_at_prime
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T11:05:32.882167+00:00
-- url     : https://prove2.me/submissions/f86d8193-b340-48db-9b28-2437e856fcfe

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeReferenceFrame_PPAssemble
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeReferenceFrame_PrincipalIdealRingAtPrime
import Theorems.Thm_PI_ScRefExists_ApP_pz_ne_bot
import Theorems.Thm_PI_ScRefExists_ApP_isLoc
import Theorems.Thm_PI_ScRefExists_ApP_isDedekind

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
variable (I : Formalism.MainNotions.S.AutInst)
namespace PI.ScRefExists.ApP
theorem _root_.solution : ApPID := by
  intro I p hp
  haveI : Fact p.Prime := ⟨hp⟩
  haveI := isLoc I (p := p)
  haveI := isDedekind I (p := p)
  exact IsDedekindDomain.isPrincipalIdealRing_localization_over_prime (𝓞 I.E) (Pz p) (pz_ne_bot hp)
end PI.ScRefExists.ApP
