-- Prove2me | solution 1 for PI.SqPairLocal.Mdl.sigC_sigC
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T10:38:53.737131+00:00
-- url     : https://prove2.me/submissions/2553c23f-b7db-4938-a931-cfd4f8988d2b

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SquarePairLocal_MemFixSub
import Definitions.Def_Formalism_LocalRingCardinality_SpanPowerMembership_Adelic
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SquarePairLocal_SigKApply
import Theorems.Thm_PI_SqPairLocal_Mdl_tau_tau
import Theorems.Thm_PI_SqPairLocal_Mdl_sigC_coe
import Theorems.Thm_PI_SqPairLocal_Mdl_sigC_cont

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain HeightOneSpectrum WithZero IsLocalRing Topology Filter
open PI PI.SqPairLocal PI.SqPairLocal.Mdl
open PI.SqPairLocal Formalism.BasicNotions.Examples₂
variable {E : Type} [Field E] [NumberField E] [StarRing E]
variable (v : HeightOneSpectrum (𝓞 E)) (hv : v.asIdeal.comap (cj E) = v.asIdeal)
include hv
namespace PI.SqPairLocal.Mdl
theorem _root_.solution (y : (v.valuation E).Completion) : sigC v hv (sigC v hv y) = y := by
  induction y using UniformSpace.Completion.induction_on with
  | hp => exact isClosed_eq ((sigC_cont v hv).comp (sigC_cont v hv)) continuous_id
  | ih a => rw [sigC_coe, sigC_coe, tau_tau]
end PI.SqPairLocal.Mdl
