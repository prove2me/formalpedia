-- Prove2me | solution 1 for PI.GGRatio.genericRatioOfBound
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T10:14:55.5463+00:00
-- url     : https://prove2.me/submissions/4955b599-57a7-4f27-9f38-63a860d36864

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_ClosedLocalOrbits_GGMirabolic
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GenericRatioBound_GenericRatioOfBound
import Theorems.Thm_PI_GGRatio_ratio_le

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PI PI.GGRatio
open Finset
open Formalism.L2.SG.GGMirabolic
namespace PI.GGRatio
theorem _root_.solution : GenericRatioOfBound := by
  intro hB hU F _ _ k ψ hψ V _ _ _ π hπ hg
  rw [hU]
  exact ratio_le (Fintype.card F) k _ Fintype.one_lt_card (hB F k ψ hψ V π hπ hg)
end PI.GGRatio
