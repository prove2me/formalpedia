-- Prove2me | solution 1 for PIW.AdelClassFin.DictInter.algebraMap_mem_intAd
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T11:18:54.465317+00:00
-- url     : https://prove2.me/submissions/102d4d53-1bf5-42b2-bd23-a0f661fa9741

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicClassFiniteness_DictPlan
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicClassFiniteness_DictInter

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PIW PIW.AdelClassFin
open Formalism.MainNotions.S PI.AdelClassFin NumberField IsDedekindDomain
open scoped TensorProduct Matrix nonZeroDivisors
open PIW.AdelClassFin.DictInter
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
namespace PIW.AdelClassFin.DictInter
theorem _root_.solution (x : 𝓞 F) : algebraMap F (Af F) (algebraMap (𝓞 F) F x) ∈ Formalism.UG.intAd F := by
  intro v
  have h1 : Valued.v (((algebraMap (𝓞 F) F x : F)) : v.adicCompletion F) ≤ 1 := by
    first
      | rw [IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_eq_valuation']
        first
          | exact v.valuation_le_one x
          | exact v.valuation_le_one F x
      | rw [IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_eq_valuation]
        first
          | exact v.valuation_le_one x
          | exact v.valuation_le_one F x
  first
    | exact h1
    | exact (IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).mpr h1
end PIW.AdelClassFin.DictInter
