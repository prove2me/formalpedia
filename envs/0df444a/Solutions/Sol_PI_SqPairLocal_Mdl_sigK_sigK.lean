-- Prove2me | solution 1 for PI.SqPairLocal.Mdl.sigK_sigK
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T10:46:50.316276+00:00
-- url     : https://prove2.me/submissions/be3d4b4a-c53d-4aeb-b4d0-eeccbc0b3bba

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SquarePairLocal_MemFixSub
import Definitions.Def_Formalism_LocalRingCardinality_SpanPowerMembership_Adelic
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SquarePairLocal_SigKApply
import Theorems.Thm_PI_SqPairLocal_Mdl_sigC_sigC
import Theorems.Thm_PI_SqPairLocal_Mdl_sigK_apply

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
theorem _root_.solution (x : v.adicCompletion E) : sigK v hv (sigK v hv x) = x := by
  rw [sigK_apply, sigK_apply, adicCompletion.toCompletion_ofCompletion, sigC_sigC]
end PI.SqPairLocal.Mdl
