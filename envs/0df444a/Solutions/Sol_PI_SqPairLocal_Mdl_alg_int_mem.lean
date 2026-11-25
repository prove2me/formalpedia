-- Prove2me | solution 1 for PI.SqPairLocal.Mdl.alg_int_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T10:23:17.431012+00:00
-- url     : https://prove2.me/submissions/957169a9-ca00-4956-baa8-4dc40e91e76e

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SquarePairLocal_SigKApply
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SquarePairLocal_PowerSeriesExpansionImageDenseWithDenominator

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
open MonoidWithZeroHom MonoidWithZeroHom.ValueGroup₀
open PI PI.SqPairLocal PI.SqPairLocal.Mdl
open PI.SqPairLocal Formalism.BasicNotions.Examples₂
variable {E : Type} [Field E] [NumberField E] [StarRing E] (v : HeightOneSpectrum (𝓞 E))
variable (hv : v.asIdeal.comap (cj E) = v.asIdeal)
include hv
namespace PI.SqPairLocal.Mdl
theorem _root_.solution (y : 𝓞 E) :
    algebraMap E (v.adicCompletion E) (algebraMap (𝓞 E) E y) ∈ v.adicCompletionIntegers E := by
  exact IsDedekindDomain.HeightOneSpectrum.coe_algebraMap_mem (𝓞 E) E v y
end PI.SqPairLocal.Mdl
