-- Prove2me | solution 1 for PI.VolStabW.SdUniqW.psiInf_add
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T11:06:32.550213+00:00
-- url     : https://prove2.me/submissions/9fbb88b6-befb-4779-a04e-89262008417d

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_RestrProd
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_TensTop
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_DensFibV
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicLocalCompactness_AdeleLC
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_SdUniq

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
open PI.VolStabW.SdUniqW
open scoped TensorProduct
open NumberField IsDedekindDomain MeasureTheory Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes PI.AdicCompletionValuation
  PI.VolFromSW
variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]
namespace PI.VolStabW.SdUniqW
theorem _root_.solution (ψ : AddChar (AF F) ℂ) (r s : Ainf F) :
    psiInf F ψ (r + s) = psiInf F ψ r * psiInf F ψ s := by
  unfold psiInf
  have h : pairA F (r + s) 0 = pairA F r 0 + pairA F s 0 := Prod.ext rfl (add_zero _).symm
  rw [h, AddChar.map_add_eq_mul]
end PI.VolStabW.SdUniqW
