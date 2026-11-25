-- Prove2me | solution 1 for PIW.AdelicOrbitU.stP
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T11:49:23.5188+00:00
-- url     : https://prove2.me/submissions/2beb1eaa-4165-4064-bfd3-df4052453bea

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicUnitaryOrbits_UnitChoice
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicUnitaryOrbits_LocalSum
import Theorems.Thm_PIW_AdelicOrbitU_uc_prod
import Theorems.Thm_PIW_AdelicOrbitU_uc_pi
import Theorems.Thm_PIW_AdelicOrbitU_uc_fin

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PIW PIW.AdelicOrbitU
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open scoped RestrictedProduct
namespace PIW.AdelicOrbitU
theorem _root_.solution : StP := by
  unfold StP
  intro F _ _
  unfold AF
  exact uc_prod (uc_pi (fun v : NumberField.InfinitePlace F => v.Completion)) (uc_fin F)
end PIW.AdelicOrbitU
