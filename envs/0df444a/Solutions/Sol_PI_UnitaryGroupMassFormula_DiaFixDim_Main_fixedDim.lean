-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.DiaFixDim.Main.fixedDim
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T11:09:49.718467+00:00
-- url     : https://prove2.me/submissions/3c66c1d5-bb1a-4714-8828-6a3265495b1c

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_SiegelMassRatios_ClassAct
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_SiegelMassRatios_ColsDim
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FixedDimensionCount_ExistsSemidirectDecomposition
import Theorems.Thm_PI_UnitaryGroupMassFormula_DiaFixDim_Main_dk_le
import Theorems.Thm_PI_UnitaryGroupMassFormula_DiaFixDim_Main_fixAt_eq
import Theorems.Thm_PI_UnitaryGroupMassFormula_DiaFixDim_Main_stabTriv_of
import Theorems.Thm_PI_UnitaryGroupMassFormula_DiaFixDim_Main_amf_dim
import Theorems.Thm_PI_UnitaryGroupMassFormula_DiaFixDim_Main_finite_dk
import Theorems.Thm_PI_UnitaryGroupMassFormula_DiaFixDim_Main_card_classes

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.DiaFixDim PI.UnitaryGroupMassFormula.DiaFixDim.Main
open Formalism.UG Formalism.L2.SG.ClassAct Module
namespace PI.UnitaryGroupMassFormula.DiaFixDim.Main
theorem _root_.solution : Formalism.L2.SG.ClassAct.FixedDim := by
  intro G _ Γ K K₀ D k _ W _ _ _ ρ χ hK hD hn hN hinv htriv hfin
  have hst1 := stabTriv_of Γ (dk K D hN) K₀ (dk_le K D K₀ hN hK hD) hn
  have hst := stabTriv_of Γ K K₀ hK hn
  have hfin1 := finite_dk Γ K D hN hfin
  rw [fixAt_eq k W Γ K D hN ρ χ hinv htriv, amf_dim k W Γ (dk K D hN) hst1 hfin1,
    amf_dim k W Γ K hst hfin, card_classes Γ K K₀ D hN hK hD hn, mul_assoc]
end PI.UnitaryGroupMassFormula.DiaFixDim.Main
