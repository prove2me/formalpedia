-- Prove2me | solution 1 for PI.Dv.GLatHermW.glatHerm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T10:28:00.212278+00:00
-- url     : https://prove2.me/submissions/e73299d9-102b-4b2f-9e69-5e21814c9552

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_DivisionRowsRationalLattice
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HermitianGroupLattices_AsAlgebraHomEG
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HermitianGroupLattices_IsCMFormEOf
import Theorems.Thm_PI_Dv_GLatHermW_isHermE_of
import Theorems.Thm_PI_Dv_GLatHermW_isCMFormE_of

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.Dv PI.Dv.GLatHermW
open PI.Dv Formalism.BasicNotions
variable {K : Type} [Field K] [NumberField K] [StarRing K] {G : Type} [Group G] [Fintype G]
namespace PI.Dv.GLatHermW
theorem _root_.solution : PI.Dv.GLatHerm := by
  intro K _ _ _ _ G _ _ T A ρ h hS hH
  exact ⟨isHermE_of T A ρ h hS hH, fun hC => isCMFormE_of T A ρ h hS hC⟩
end PI.Dv.GLatHermW
