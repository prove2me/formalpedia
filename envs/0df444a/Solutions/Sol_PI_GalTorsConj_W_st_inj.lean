-- Prove2me | solution 1 for PI.GalTorsConj.W.st_inj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T06:56:41.313676+00:00
-- url     : https://prove2.me/submissions/970783ff-84d1-4295-9ea7-217ad2cd1f8e

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GaloisTorsionConjugacy_WpBridge
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_MulStableIntegral
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GaloisTorsionConjugacy_StAddRight
import Theorems.Thm_PI_GalTorsConj_W_pInj
import Theorems.Thm_PI_GalTorsConj_W_rho_inj

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
theorem _root_.solution {t u s : ℂ} (h1 : St L L' M ρ t s) (h2 : St L L' M ρ u s) :
    t - u ∈ L.lattice := by
  rcases h1 with ⟨a1, b1⟩ | ⟨a1, b1, hx1, hy1, e1, f1⟩
  · rcases h2 with ⟨a2, b2⟩ | ⟨a2, b2, _, _, _, _⟩
    · exact L.lattice.sub_mem a1 a2
    · exact absurd b1 b2
  · rcases h2 with ⟨a2, b2⟩ | ⟨a2, b2, hx2, hy2, e2, f2⟩
    · exact absurd b2 b1
    · have gx := rho_inj (e1.symm.trans e2)
      have gy := rho_inj (f1.symm.trans f2)
      exact pInj L a1 a2 (congrArg Subtype.val gx) (congrArg Subtype.val gy)
end PI.GalTorsConj.W
