-- Prove2me | solution 1 for PIW.AdelClassFin.stH_of_parts
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T12:03:34.381415+00:00
-- url     : https://prove2.me/submissions/b1d5a02c-6a15-4d47-980a-6df2acac6b5a

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicClassFiniteness_StGenusOf
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicClassFiniteness_HformSelfStar
import Theorems.Thm_PIW_AdelClassFin_hl_all
import Theorems.Thm_PIW_AdelClassFin_stH_of_hl

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PIW PIW.AdelClassFin
open Formalism.UG NumberField
open scoped Matrix
namespace PIW.AdelClassFin
theorem _root_.solution (hS : PartShort) (hU : PartUnits) (hI : PartIso) (hP : PartSplit) : StH :=
  stH_of_hl fun F E _ _ _ _ _ _ hc m => hl_all hS hU hI hP F E hc m
end PIW.AdelClassFin
