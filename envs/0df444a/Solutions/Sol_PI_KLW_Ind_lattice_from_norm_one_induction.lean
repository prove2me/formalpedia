-- Prove2me | solution 1 for PI.KLW.Ind.lattice_from_norm_one_induction
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T10:15:31.846274+00:00
-- url     : https://prove2.me/submissions/759f1f30-3c19-470c-95ae-c0ec19758dcb

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalLatticeIsomorphism_IndBasic
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalLatticeIsomorphism_LatticeFromNormOneInduction
import Theorems.Thm_PI_KLW_Ind_latIso_card

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
open PI PI.KLW PI.KLW.Ind
open PI.KLW
namespace PI.KLW.Ind
theorem _root_.solution : LatticeFromNormOne := by
  intro hN K _ _ c p ι _ L hK hc hp hs hL hS
  exact latIso_card hN c p hK hc hp hs _ ι rfl L hL hS
end PI.KLW.Ind
