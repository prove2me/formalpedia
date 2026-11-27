-- Prove2me | solution 1 for PI.VolStabSW.SdUniqW.psiInf_add
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-27T05:17:51.504139+00:00
-- url     : https://prove2.me/submissions/e1d998f2-3ab2-4e52-a7d8-a6be3be8caad

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_RestrProd
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_TensTop
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_DensFibV
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicLocalCompactness_AdeleLC
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_SdUniq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.VolStabSW
open PI.VolStabSW.SdUniqW
open scoped TensorProduct
open NumberField IsDedekindDomain MeasureTheory Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes PI.AdicCompletionValuation
  PI.VolFromSW
variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]
namespace PI.VolStabSW.SdUniqW
theorem _root_.solution (ψ : AddChar (AF F) ℂ) (r s : Ainf F) :
    psiInf F ψ (r + s) = psiInf F ψ r * psiInf F ψ s := by
  have e : pairA F (r + s) 0 = pairA F r 0 + pairA F s 0 := by
    show (r + s, (0 : Af F)) = (r + s, (0 : Af F) + 0)
    rw [add_zero]
  unfold psiInf
  rw [e, AddChar.map_add_eq_mul]
end PI.VolStabSW.SdUniqW
