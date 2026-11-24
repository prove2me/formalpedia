-- Prove2me | solution 1 for PI.SqPairLocal.Mdl.sigC_cont
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T21:47:15.676024+00:00
-- url     : https://prove2.me/submissions/63e4d251-73c2-4bc6-b743-9cbdcf400680

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SquarePairLocal_MemFixSub
import Definitions.Def_Formalism_LocalRingCardinality_SpanPowerMembership_Adelic
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SquarePairLocal_SigKApply

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
theorem _root_.solution : Continuous (sigC v hv) := by
  rw [sigC, UniformSpace.Completion.coe_mapRingHom]
  exact UniformSpace.Completion.continuous_map
end PI.SqPairLocal.Mdl
