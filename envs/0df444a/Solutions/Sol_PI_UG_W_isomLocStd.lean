-- Prove2me | solution 1 for PI.UG.W.isomLocStd
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T15:10:43.874173+00:00
-- url     : https://prove2.me/submissions/ecb9af95-0e81-4276-9109-a64125041e74

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnimodularGenus_UnimodLocalOfLocDual
import Definitions.Def_Formalism_PeriodIntegrals_HermitianGenusExtension_SemilocalHermitianLattices_ExistsIsomLoc
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnimodularGenus_Bridge
import Theorems.Thm_PI_UG_W_hStd_isSymm
import Theorems.Thm_PI_UG_W_stdLat_isOrtho
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L3_exists_isom_loc
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L3_stdLat_isOrtho


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PI PI.UG PI.UG.W
open NumberField
namespace PI.UG.W
theorem _root_.solution : IsomLocStd := by
  intro E _ _ _ n hE N hN p hp hu
  exact ReciprocityTheory.ChartRestriction.L3.exists_isom_loc hE (hStd_isSymm E n) (stdLat_isOrtho E n) hN p hp hu
end PI.UG.W
