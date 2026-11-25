-- Prove2me | solution 1 for PI.GalTorsConj.W.st_unique
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T06:56:25.700574+00:00
-- url     : https://prove2.me/submissions/afd8c53f-b3fb-48d5-a679-5e88c0726d66

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GaloisTorsionConjugacy_WpBridge
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_MulStableIntegral
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GaloisTorsionConjugacy_StAddRight
import Theorems.Thm_PI_GalTorsConj_W_pInj

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.GalTorsConj PI.GalTorsConj.W
open Formalism.L2.Th1.F
variable {L L' : PeriodPair} {M : IntermediateField ℚ ℂ} {ρ : M →ₐ[ℚ] ℂ}
namespace PI.GalTorsConj.W
theorem _root_.solution {t t₁ t₂ : ℂ} (h1 : St L L' M ρ t t₁) (h2 : St L L' M ρ t t₂) :
    t₁ - t₂ ∈ L'.lattice := by
  rcases h1 with ⟨a1, b1⟩ | ⟨a1, b1, hx1, hy1, e1, f1⟩
  · rcases h2 with ⟨a2, b2⟩ | ⟨a2, _, _, _, _, _⟩
    · exact L'.lattice.sub_mem b1 b2
    · exact absurd a1 a2
  · rcases h2 with ⟨a2, _⟩ | ⟨a2, b2, hx2, hy2, e2, f2⟩
    · exact absurd a2 a1
    · exact pInj L' b1 b2 (by rw [e1, e2]) (by rw [f1, f2])
end PI.GalTorsConj.W
