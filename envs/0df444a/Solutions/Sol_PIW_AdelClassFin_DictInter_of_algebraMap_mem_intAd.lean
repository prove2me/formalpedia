-- Prove2me | solution 1 for PIW.AdelClassFin.DictInter.of_algebraMap_mem_intAd
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T11:18:54.677877+00:00
-- url     : https://prove2.me/submissions/f4488ac1-7003-42f7-9fd9-697b16965bb2

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
theorem _root_.solution (f : F) (h : algebraMap F (Af F) f ∈ Formalism.UG.intAd F) :
    f ∈ (algebraMap (𝓞 F) F).range := by
  refine IsDedekindDomain.HeightOneSpectrum.mem_integers_of_valuation_le_one (R := 𝓞 F) (K := F) f ?_
  intro v
  have hv : Valued.v ((f : F) : v.adicCompletion F) ≤ 1 := h v
  first
    | rwa [IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_eq_valuation'] at hv
    | rwa [IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_eq_valuation] at hv
end PIW.AdelClassFin.DictInter
