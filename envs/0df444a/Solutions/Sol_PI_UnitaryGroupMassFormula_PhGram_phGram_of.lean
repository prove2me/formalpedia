-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.PhGram.phGram_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T10:41:31.980254+00:00
-- url     : https://prove2.me/submissions/b196192f-3309-4027-b0d0-9c4cc466d233

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GramSubstitutionIntegral_IntegralSubst
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GramSubstitutionIntegral_PhGramOf

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Classical
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.PhGram
open PI.FglGram
namespace PI.UnitaryGroupMassFormula.PhGram
theorem _root_.solution (hC : Column) (hG : Gather) : PI.FglGram.PhGram := by
  intro p _ l ex ph S hD hsw hiM hiA hN hCj hB κ _ k A hA
  have H : Hyps l ex ph S := ⟨hD, hsw, hiM, hiA, hN, hCj, hB⟩
  exact hG p l ex ph S H (hC p l ex ph S H) κ k A hA
end PI.UnitaryGroupMassFormula.PhGram
