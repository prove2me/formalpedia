-- Prove2me | solution 1 for PI.SqPairLocal.Mdl.tau_tau
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T10:23:59.656108+00:00
-- url     : https://prove2.me/submissions/aec5e348-abb3-4bb5-a7fc-9c1fbd74643e

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
omit hv
namespace PI.SqPairLocal.Mdl
theorem _root_.solution (x : WithVal (v.valuation E)) : tau v (tau v x) = x := by
  rw [tau_apply, tau_apply, WithVal.ofVal_toVal, star_star, WithVal.toVal_ofVal]
end PI.SqPairLocal.Mdl
