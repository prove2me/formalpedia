-- Prove2me | solution 1 for P2M_PI_VolStabW_SdTestInfW_continuous_psiInf__007137ef755b
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T08:51:21.406783+00:00
-- url     : https://prove2.me/submissions/d3fb63d0-2b2c-49cb-827a-050f5acbbb60

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_SdUniq
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_DensInfAll
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_RealCharacter
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_SdTestInf

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.VolStabW
open PI.VolStabW.SdTestInfW
open MeasureTheory Complex Filter Topology
open scoped TensorProduct
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes PI.AdicCompletionValuation PI.VolFromSW SdUniqW
namespace PI.VolStabW.SdTestInfW
theorem _root_.solution {F : Type} [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ)
    (hψ : Continuous ψ) : Continuous (psiInf F ψ) := by
  have : Continuous fun x : Ainf F => ((x, (0 : Af F)) : Ainf F × Af F) :=
    continuous_id.prodMk continuous_const
  exact hψ.comp this
end PI.VolStabW.SdTestInfW
