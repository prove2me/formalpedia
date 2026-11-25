-- Prove2me | solution 1 for PI.LocJacOrd.W.locJacOrd_of_sd
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T10:18:48.058704+00:00
-- url     : https://prove2.me/submissions/02ef9ef7-ee27-4c7b-b442-47d152b95925

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalJacobianOrder_SecondCountableFv
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalJacobianOrder_LocJacOrdOfSd
import Theorems.Thm_PI_LocJacOrd_W_absMul_holds
import Theorems.Thm_PI_LocJacOrd_W_arithO_holds
import Theorems.Thm_PI_LocJacOrd_W_locJacOrd_of
import Theorems.Thm_PI_LocJacOrd_W_volPO_of
import Theorems.Thm_PI_LocJacOrd_W_volUO_of
import Theorems.Thm_PI_LocJacOrd_W_volZZO_of


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.LocJacOrd PI.LocJacOrd.W
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory NumberField IsDedekindDomain PI.LocJacOrd
namespace PI.LocJacOrd.W
theorem _root_.solution {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (ψ : AddChar (AF F) ℂ) (v : HeightOneSpectrum (𝓞 F)) (h0 : SdNormO (E := E) ψ v)
    (hB : BoxScale) : LocJacOrd (E := E) ψ v :=
  locJacOrd_of ψ v h0 (volZZO_of v hB absMul_holds) (volUO_of v hB absMul_holds)
    (volPO_of v hB absMul_holds) (arithO_holds v)
end PI.LocJacOrd.W
