-- Prove2me | solution 1 for PI.SqPairLocal.Mdl.sigK_int
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T10:53:39.603192+00:00
-- url     : https://prove2.me/submissions/e8fa1968-37fd-4f57-b6f1-e25badd7b956

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SquarePairLocal_SigKApply
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SquarePairLocal_PowerSeriesExpansionImageDenseWithDenominator
import Theorems.Thm_PI_SqPairLocal_Mdl_sigK_alg


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
    sigK v hv (algebraMap E (v.adicCompletion E) (algebraMap (𝓞 E) E y)) =
      algebraMap E (v.adicCompletion E) (algebraMap (𝓞 E) E (cj E y)) := by
  rw [sigK_alg v hv]; rfl
end PI.SqPairLocal.Mdl
