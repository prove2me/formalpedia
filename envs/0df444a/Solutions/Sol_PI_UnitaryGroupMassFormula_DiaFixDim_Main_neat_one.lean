-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.DiaFixDim.Main.neat_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T10:49:25.595919+00:00
-- url     : https://prove2.me/submissions/07f9bec6-cbdd-4269-938c-8672e022d494

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
theorem _root_.solution {G : Type} [Group G] {Γ K₀ : Subgroup G} (hn : IsNeat Γ K₀) {x γ : G}
    (hγ : γ ∈ Γ) (h : x⁻¹ * γ * x ∈ K₀) : γ = 1 := by
  have hm : (⟨γ, hγ⟩ : Γ) ∈ stabAt Γ K₀ x := h
  rw [hn x] at hm
  exact congrArg Subtype.val hm
end PI.UnitaryGroupMassFormula.DiaFixDim.Main
