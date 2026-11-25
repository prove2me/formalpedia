-- Prove2me | solution 1 for PI.SqPairLocal.Mdl.sigK_alg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T10:29:52.872708+00:00
-- url     : https://prove2.me/submissions/2d01cbf2-2419-4650-974c-c1e8bca63fe0

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SquarePairLocal_MemFixSub
import Definitions.Def_Formalism_LocalRingCardinality_SpanPowerMembership_Adelic
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SquarePairLocal_SigKApply
import Theorems.Thm_PI_SqPairLocal_Mdl_sigC_coe

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
theorem _root_.solution (a : E) :
    sigK v hv (algebraMap E (v.adicCompletion E) a) = algebraMap E (v.adicCompletion E) (star a) := by
  show adicCompletion.ofCompletion (sigC v hv _) = _
  erw [sigC_coe]
  rfl
end PI.SqPairLocal.Mdl
