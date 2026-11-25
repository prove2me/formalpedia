-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.UJClassMass.algebraMap_int_intAf
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T10:54:30.918507+00:00
-- url     : https://prove2.me/submissions/b602ca2c-e118-48a6-a3b9-4798c0e33910

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryClassMass_PSurjS
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryClassMass_OneSubEvTInvInt
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryClassMass_AlgebraMapIntIntAf

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField PI.UJClassFin PI.UJClassMass Formalism.HermitianLatticesTheory IsDedekindDomain PI.UnitaryGroupMassFormula.UJClassFin
open scoped TensorProduct
noncomputable section
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.UJClassMass
variable {F : Type} [Field F] [NumberField F]
namespace PI.UnitaryGroupMassFormula.UJClassMass
theorem _root_.solution (t : 𝓞 F) : algebraMap F (Af F) (algebraMap (𝓞 F) F t) ∈ intAf F := by
  intro w
  show (algebraMap F (Af F) (algebraMap (𝓞 F) F t)) w ∈ w.adicCompletionIntegers F
  rw [af_alg_apply, HeightOneSpectrum.mem_adicCompletionIntegers]
  have e1 : algebraMap F (w.adicCompletion F) (algebraMap (𝓞 F) F t) =
      ((algebraMap (𝓞 F) F t : F) : w.adicCompletion F) := rfl
  rw [e1, HeightOneSpectrum.valuedAdicCompletion_eq_valuation', HeightOneSpectrum.valuation_of_algebraMap]
  exact HeightOneSpectrum.intValuation_le_one w t
end PI.UnitaryGroupMassFormula.UJClassMass
