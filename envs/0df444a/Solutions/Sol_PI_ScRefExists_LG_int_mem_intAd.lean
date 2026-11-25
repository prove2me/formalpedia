-- Prove2me | solution 1 for PI.ScRefExists.LG.int_mem_intAd
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T10:27:36.243409+00:00
-- url     : https://prove2.me/submissions/3ce18827-17c7-44df-8174-f6342485486d

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeReferenceFrame_Development
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeReferenceFrame_LocGlob

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField Formalism.MainNotions.S IsDedekindDomain
open scoped TensorProduct nonZeroDivisors
open PI PI.ScRefExists PI.ScRefExists.LG
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
namespace PI.ScRefExists.LG
theorem _root_.solution (r : 𝓞 F) : algebraMap F (Af F) (algebraMap (𝓞 F) F r) ∈ Formalism.UG.intAd F := by
  intro v
  show ((algebraMap (𝓞 F) F r : F) : v.adicCompletion F) ∈ v.adicCompletionIntegers F
  rw [HeightOneSpectrum.mem_adicCompletionIntegers, HeightOneSpectrum.valuedAdicCompletion_eq_valuation']
  exact v.valuation_le_one r
end PI.ScRefExists.LG
