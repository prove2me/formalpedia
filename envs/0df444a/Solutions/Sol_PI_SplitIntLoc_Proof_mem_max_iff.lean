-- Prove2me | solution 1 for PI.SplitIntLoc.Proof.mem_max_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T10:22:08.415742+00:00
-- url     : https://prove2.me/submissions/dbad3003-de42-46ba-9fe6-464648ff4e48

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_SplitIntLoc
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SplitPrimeIntegers_EmbMemOfIsIntegral

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum
open scoped TensorProduct
noncomputable section
open PI PI.SplitIntLoc PI.SplitIntLoc.Proof
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (v : HeightOneSpectrum (𝓞 F))
namespace PI.SplitIntLoc.Proof
theorem _root_.solution (z : (v.adicCompletionIntegers F)) : z ∈ IsLocalRing.maximalIdeal (v.adicCompletionIntegers F) ↔ Valued.v (z : (v.adicCompletion F)) < 1 := by
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, (intsV v).isUnit_iff_valuation_eq_one]
  exact ⟨fun h => lt_of_le_of_ne ((intsV v).map_le_one z) h, ne_of_lt⟩
end PI.SplitIntLoc.Proof
