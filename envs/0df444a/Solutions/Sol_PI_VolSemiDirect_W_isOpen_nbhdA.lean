-- Prove2me | solution 1 for PI.VolSemiDirect.W.isOpen_nbhdA
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T11:03:15.618504+00:00
-- url     : https://prove2.me/submissions/1f975449-cde5-45a5-9ae3-c4920147f74f

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SemidirectVolume_ClosedStep
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdicCompactDensity_ExistsNatLocal
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SemidirectVolume_EqZeroOfMemNbhdA
import Theorems.Thm_PI_VolSemiDirect_W_continuous_norm_inf
import Theorems.Thm_PI_AdCpctDenWork_isOpen_intAd


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.VolSemiDirect PI.VolSemiDirect.W
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub NumberField IsDedekindDomain MeasureTheory
  IsDedekindDomain.HeightOneSpectrum
open scoped TensorProduct Matrix
variable (F : Type) [Field F] [NumberField F]
namespace PI.VolSemiDirect.W
theorem _root_.solution : IsOpen (nbhdA F) :=
  (isOpen_lt ((continuous_norm_inf F).comp continuous_fst) continuous_const).inter
    (PI.AdCpctDenWork.isOpen_intAd.preimage continuous_snd)
end PI.VolSemiDirect.W
