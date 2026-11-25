-- Prove2me | solution 1 for PI.LocDualGen.EpG.quadraticSelfDual
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T10:08:53.083779+00:00
-- url     : https://prove2.me/submissions/6e4e3339-9116-44ec-8e15-09f752d1bb86

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalDualGenerator_FpDualUnram
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalDualGenerator_EpSelfDualField
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalDualGenerator_EpSelfDualSplit
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalDualGenerator_EpSelfDualCase
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalDualGenerator_EpSelfDual
import Theorems.Thm_PI_LocDualGen_EpG_field_version
import Theorems.Thm_PI_LocDualGen_EpC_dichotomy
import Theorems.Thm_PI_LocDualGen_EpS_selfDual_split


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option linter.style.haveILetI false
noncomputable section
open ValuativeRel Module
open PI PI.LocDualGen PI.LocDualGen.EpG
namespace PI.LocDualGen.EpG
theorem _root_.solution : PI.LocDualGen.W.EpSelfDual := by
  intro K _ _ _ L _ _ hK hC _ hr hred O hO hU x
  haveI := hK
  haveI := hC
  rcases PI.LocDualGen.EpC.dichotomy hr hred with hF | ⟨e, he, h0, h1⟩
  · letI : Field L := hF.toField
    exact field_version K L hr O hO hU x
  · have key := PI.LocDualGen.EpS.selfDual_split hr e he h0 h1 x
    simpa only [hO] using key
end PI.LocDualGen.EpG
