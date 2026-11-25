-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.DiaFixDim.Main.dk_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T10:40:30.840352+00:00
-- url     : https://prove2.me/submissions/c6454c30-c026-4585-a5f6-e1174543c05f

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
theorem _root_.solution {G : Type} [Group G] (K D K₀ : Subgroup G) (hN : Normalises D K) (hK : K ≤ K₀)
    (hD : D ≤ K₀) : dk K D hN ≤ K₀ := by
  intro g hg
  obtain ⟨δ, hδ, κ, hκ, rfl⟩ := (mem_dk K D hN).1 hg
  exact K₀.mul_mem (hD hδ) (hK hκ)
end PI.UnitaryGroupMassFormula.DiaFixDim.Main
