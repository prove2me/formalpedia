-- Prove2me | solution 1 for PI.ScPsiExists.UnitaryGroupMassFormula.alg_int_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T13:00:01.043871+00:00
-- url     : https://prove2.me/submissions/4c756699-2385-4952-860f-7abab81e068e

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_ScPsiExists
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_EmbeddingTraceSumAlt_NormUnitsOfCalculation

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain Formalism.MainNotions.S
open scoped TensorProduct
open PI PI.ScPsiExists PI.ScPsiExists.UnitaryGroupMassFormula
namespace PI.ScPsiExists.UnitaryGroupMassFormula
theorem _root_.solution (F : Type) [Field F] [NumberField F] (d : 𝓞 F) :
    algebraMap F (Af F) (algebraMap (𝓞 F) F d) ∈ Formalism.UG.intAd F := by
  intro v
  show (algebraMap F (Af F) (algebraMap (𝓞 F) F d)) v ∈ v.adicCompletionIntegers F
  rw [FiniteAdeleRing.algebraMap_apply, HeightOneSpectrum.mem_adicCompletionIntegers,
    HeightOneSpectrum.valuedAdicCompletion_eq_valuation']
  exact HeightOneSpectrum.valuation_le_one v d
end PI.ScPsiExists.UnitaryGroupMassFormula
