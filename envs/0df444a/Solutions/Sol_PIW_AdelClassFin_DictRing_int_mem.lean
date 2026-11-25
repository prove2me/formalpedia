-- Prove2me | solution 1 for PIW.AdelClassFin.DictRing.int_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T11:23:06.600241+00:00
-- url     : https://prove2.me/submissions/9a783567-8496-45dd-b8a2-d662e7ca7b99

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicClassFiniteness_DictPlan
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StrongApproximation_DedekindLFunctions
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicClassFiniteness_DictRing

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
open scoped TensorProduct Matrix
open PIW.AdelClassFin.DictRing
variable {F : Type} [Field F] [NumberField F]
namespace PIW.AdelClassFin.DictRing
theorem _root_.solution (r : 𝓞 F) (v : HeightOneSpectrum (𝓞 F)) :
    algebraMap (𝓞 F) (v.adicCompletion F) r ∈ v.adicCompletionIntegers F := by
  rw [IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers,
    IsScalarTower.algebraMap_apply (𝓞 F) F (v.adicCompletion F)]
  have h : Valued.v (algebraMap F (v.adicCompletion F) (algebraMap (𝓞 F) F r)) =
      v.valuation F (algebraMap (𝓞 F) F r) :=
    IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v (algebraMap (𝓞 F) F r)
  rw [h]
  exact v.valuation_le_one r
end PIW.AdelClassFin.DictRing
