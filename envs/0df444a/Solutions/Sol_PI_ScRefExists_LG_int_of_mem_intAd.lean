-- Prove2me | solution 1 for PI.ScRefExists.LG.int_of_mem_intAd
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T10:26:33.104621+00:00
-- url     : https://prove2.me/submissions/a9001e50-57f5-433e-b4fe-9710a96b94b1

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
theorem _root_.solution (x : F) (h : algebraMap F (Af F) x ∈ Formalism.UG.intAd F) :
    x ∈ (algebraMap (𝓞 F) F).range := by
  refine HeightOneSpectrum.mem_integers_of_valuation_le_one F x fun v => ?_
  have hv : ((x : F) : v.adicCompletion F) ∈ v.adicCompletionIntegers F := h v
  rwa [HeightOneSpectrum.mem_adicCompletionIntegers,
    HeightOneSpectrum.valuedAdicCompletion_eq_valuation'] at hv
end PI.ScRefExists.LG
