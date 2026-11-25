-- Prove2me | solution 1 for PI.ScRefExists.Id.mkA_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T10:25:53.239622+00:00
-- url     : https://prove2.me/submissions/b98ab3fe-37c3-45f6-bfd1-ef629701f39a

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeReferenceFrame_IdemLiftOfSteps
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeReferenceFrame_IdemAd
import Theorems.Thm_PI_ScRefExists_Id_mkA_apply

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
open PI PI.ScRefExists PI.ScRefExists.Id
variable {F : Type} [Field F] [NumberField F]
namespace PI.ScRefExists.Id
theorem _root_.solution (c : ∀ v : HeightOneSpectrum (𝓞 F), v.adicCompletion F)
    (hc : ∀ v, Valued.v (c v) ≤ 1) : mkA c hc ∈ Formalism.UG.intAd F := by
  unfold Formalism.UG.intAd
  show ∀ v, mkA c hc v ∈ HeightOneSpectrum.adicCompletionIntegers F v
  intro v
  rw [mkA_apply]
  exact memO.2 (hc v)
end PI.ScRefExists.Id
