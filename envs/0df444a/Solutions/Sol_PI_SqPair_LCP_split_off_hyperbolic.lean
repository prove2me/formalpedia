-- Prove2me | solution 1 for PI.SqPair.LCP.split_off_hyperbolic
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T10:28:00.183295+00:00
-- url     : https://prove2.me/submissions/4e7aea80-d60f-480f-9e9b-8f41e8519165

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalCartanPairs_SplPlane
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalCartanPairs_PiNonunit
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalCartanPairs_SplOff
import Theorems.Thm_PI_LocCartanPair_splPlane


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.SqPair PI.SqPair.LCP
namespace PI.SqPair.LCP
theorem _root_.solution : SplitOff := by
  intro R _ _ _ ι κ _ _ _ _ hc A hA x y hxx hyy hxy
  obtain ⟨u, v, A₁, h1, h2, h3, h4, h5, -, -⟩ := PI.LocCartanPair.splPlane hc A hA x y hxx hyy hxy
  exact ⟨u, v, A₁, h1, h2, h3, h4, h5⟩
end PI.SqPair.LCP
