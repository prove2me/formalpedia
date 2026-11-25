-- Prove2me | solution 1 for PI.KLW.normOne_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T10:30:15.948696+00:00
-- url     : https://prove2.me/submissions/7a400a83-0c9f-4454-8c20-e6bd19856400

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalLatticeIsomorphism_NormOneB
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalLatticeIsomorphism_NormOneC
import Theorems.Thm_PI_KLW_NO_normOne_of_pair

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open NumberField
open PI PI.KLW
namespace PI.KLW
theorem _root_.solution (h : PairOne) : NormOne := by
  intro K _ _ c p ι _ _ L hK hc hp hs hU hS
  obtain ⟨x, hx, y, hy, hxy⟩ := h K c p ι L hK hc hp hs hU hS
  exact NO.normOne_of_pair c p L hK hc hp hs hU hS hx hy hxy
end PI.KLW
