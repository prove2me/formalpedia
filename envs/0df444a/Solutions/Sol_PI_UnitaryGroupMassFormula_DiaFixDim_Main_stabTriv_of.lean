-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.DiaFixDim.Main.stabTriv_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T10:46:16.439796+00:00
-- url     : https://prove2.me/submissions/9e201035-8357-42df-b457-a2d6da178720

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_SiegelMassRatios_ClassAct
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_SiegelMassRatios_ColsDim
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FixedDimensionCount_ExistsSemidirectDecomposition
import Theorems.Thm_PI_UnitaryGroupMassFormula_DiaFixDim_Main_neat_one

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
theorem _root_.solution {G : Type} [Group G] (Γ K₁ K₀ : Subgroup G) (h : K₁ ≤ K₀)
    (hn : IsNeat Γ K₀) : Formalism.L2.SG.ColsDim.StabTriv Γ.subtype K₁ := by
  intro x γ hx
  exact Subtype.ext (neat_one hn γ.2 (h hx))
end PI.UnitaryGroupMassFormula.DiaFixDim.Main
