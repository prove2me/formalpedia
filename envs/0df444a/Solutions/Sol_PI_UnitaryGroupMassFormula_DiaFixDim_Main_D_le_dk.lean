-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.DiaFixDim.Main.D_le_dk
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T10:40:07.260453+00:00
-- url     : https://prove2.me/submissions/4f54953c-36ae-473b-ab34-f9b71b01b519

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_SiegelMassRatios_ClassAct
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_SiegelMassRatios_ColsDim
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FixedDimensionCount_ExistsSemidirectDecomposition

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
theorem _root_.solution {G : Type} [Group G] (K D : Subgroup G) (hN : Normalises D K) : D ≤ dk K D hN :=
  fun δ hδ => (mem_dk K D hN).2 ⟨δ, hδ, 1, K.one_mem, by simp⟩
end PI.UnitaryGroupMassFormula.DiaFixDim.Main
