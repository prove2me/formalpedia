-- Prove2me | solution 1 for PI.ScRefExists.ApP.isFrac
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-27T05:17:44.183944+00:00
-- url     : https://prove2.me/submissions/c6c4fd8a-d818-4be6-bcfd-6d5c6a506152

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeReferenceFrame_PPAssemble
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeReferenceFrame_PrincipalIdealRingAtPrime
import Theorems.Thm_PI_ScRefExists_ApP_isLoc

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
theorem _root_.solution {p : ℕ} [Fact p.Prime] : IsFractionRing (Ap I p) I.E := by
  haveI := isLoc I (p := p)
  exact IsFractionRing.isFractionRing_of_isDomain_of_isLocalization
    (Algebra.algebraMapSubmonoid (𝓞 I.E) (Pz p).primeCompl) (Ap I p) I.E
end PI.ScRefExists.ApP
