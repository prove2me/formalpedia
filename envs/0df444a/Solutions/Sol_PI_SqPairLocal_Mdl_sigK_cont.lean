-- Prove2me | solution 1 for PI.SqPairLocal.Mdl.sigK_cont
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T10:23:55.340841+00:00
-- url     : https://prove2.me/submissions/75a46a6f-4504-45e1-b4cb-9832a1304b0d

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SquarePairLocal_MemFixSub
import Definitions.Def_Formalism_LocalRingCardinality_SpanPowerMembership_Adelic
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SquarePairLocal_SigKApply
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
theorem _root_.solution : Continuous (sigK v hv) := by
  have : (sigK v hv : v.adicCompletion E → v.adicCompletion E) =
      adicCompletion.ofCompletion ∘ (sigC v hv) ∘ adicCompletion.toCompletion := rfl
  rw [this]
  exact (adicCompletion.continuous_ofCompletion E v).comp ((sigC_cont v hv).comp
    (adicCompletion.continuous_toCompletion E v))
end PI.SqPairLocal.Mdl
