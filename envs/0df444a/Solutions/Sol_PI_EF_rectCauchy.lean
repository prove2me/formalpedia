-- Prove2me | solution 1 for PI.EF.rectCauchy
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-27T05:19:08.770573+00:00
-- url     : https://prove2.me/submissions/d2c4c131-ab53-4183-b666-9a1a50da7b74

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ExplicitFormula_GoodHeightExists
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ExplicitFormula_RectIntEqZeroOfDifferentiableOn
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ExplicitFormula_RectProofs
import Theorems.Thm_PI_EF_Rect_rectInt_div_sub


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PI PI.EF
open Complex
namespace PI.EF
theorem _root_.solution : RectCauchy := by
  intro x₀ x₁ y₀ y₁ h w h1 h2 h3 h4 hh
  exact Rect.rectInt_div_sub (z := ⟨x₀, y₀⟩) (w := ⟨x₁, y₁⟩) (p := w) ⟨h1, h2, h3, h4⟩ hh
end PI.EF
