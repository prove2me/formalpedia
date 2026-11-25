-- Prove2me | solution 1 for PI.SplitIntLoc.Proof.main
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T11:12:17.995928+00:00
-- url     : https://prove2.me/submissions/1fd50f36-3a2a-4155-9745-517c1e68bd3b

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_SplitIntLoc
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SplitPrimeIntegers_EmbMemOfIsIntegral
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SplitPrimeIntegers_ExistsUnitDiff
import Theorems.Thm_PI_SplitIntLoc_Proof_sup_dir
import Theorems.Thm_PI_SplitIntLoc_Proof_sub_dir


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
  {v : HeightOneSpectrum (𝓞 F)} (spl : E ⊗[F] (v.adicCompletion F) ≃+* (v.adicCompletion F) × (v.adicCompletion F))
namespace PI.SplitIntLoc.Proof
theorem _root_.solution : PI.SplitIntLoc := by
  intro F E _ _ _ _ _ v spl hspl x
  exact ⟨fun hx => sub_dir spl hspl x hx, fun h => sup_dir spl hspl x h.1 h.2⟩
end PI.SplitIntLoc.Proof
