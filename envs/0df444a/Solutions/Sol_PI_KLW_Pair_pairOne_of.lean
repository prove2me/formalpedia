-- Prove2me | solution 1 for PI.KLW.Pair.pairOne_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T10:37:21.273693+00:00
-- url     : https://prove2.me/submissions/8e81f8f2-392c-4b12-a945-d784c2140096

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalLatticeIsomorphism_NormOneP
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalLatticeIsomorphism_NormOneA
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalLatticeIsomorphism_IndBasic
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalLatticeIsomorphism_PairOfEps
import Theorems.Thm_PI_KLW_Pair_pair_of_eps
import Theorems.Thm_PI_KLW_Pair_ne_of_split
import Theorems.Thm_PI_KLW_NO_ne_of_split


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
open PI PI.KLW PI.KLW.Pair
open PI.KLW
namespace PI.KLW.Pair
theorem _root_.solution (h : EpsSplit) : PairOne := by
  intro K _ _ c p ι _ _ L hK hc hp hs hL hS
  obtain ⟨ε, hε, hsum, hδ⟩ := h K c p hK hc hp hs 2
  exact pair_of_eps c hc hK (ne_of_split hs) hp hL hS hε hsum hδ
end PI.KLW.Pair
