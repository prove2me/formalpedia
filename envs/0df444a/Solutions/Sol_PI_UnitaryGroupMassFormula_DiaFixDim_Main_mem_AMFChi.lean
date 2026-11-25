-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.DiaFixDim.Main.mem_AMFChi
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T10:46:14.031299+00:00
-- url     : https://prove2.me/submissions/db2c73bc-d51f-4d4a-99ea-71d112361109

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
theorem _root_.solution {G : Type} [Group G] (k : Type) [Field k] {W : Type} [AddCommGroup W]
    [Module k W] (Γ K : Subgroup G) (ρ : Representation k Γ W) (χ : K →* kˣ) (f : G → W) :
    f ∈ AMFChi k Γ K ρ χ ↔
      ∀ γ : Γ, ∀ g : G, ∀ κ : K, f ((γ : G) * g * κ) = ((χ κ : kˣ) : k) • ρ γ (f g) := Iff.rfl
end PI.UnitaryGroupMassFormula.DiaFixDim.Main
