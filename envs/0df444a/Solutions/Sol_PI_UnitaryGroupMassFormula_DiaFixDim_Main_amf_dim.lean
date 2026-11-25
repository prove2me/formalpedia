-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.DiaFixDim.Main.amf_dim
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T10:40:26.592967+00:00
-- url     : https://prove2.me/submissions/0545cb80-a007-4069-9651-881840cffa4a

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_SiegelMassRatios_ClassAct
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_SiegelMassRatios_ColsDim
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FixedDimensionCount_ExistsSemidirectDecomposition
import Theorems.Thm_Formalism_L2_SG_ColsDim_equi_dim
import Theorems.Thm_Formalism_L2_SG_ColsDim_equi_subtype


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
theorem _root_.solution {G : Type} [Group G] (k : Type) [Field k] (W : Type) [AddCommGroup W]
    [Module k W] [FiniteDimensional k W] (Γ K₁ : Subgroup G)
    (hst : Formalism.L2.SG.ColsDim.StabTriv Γ.subtype K₁) (hfin : Finite (ClassSet Γ K₁))
    (ρ : Representation k Γ W) (χ : K₁ →* kˣ) :
    finrank k (AMFChi k Γ K₁ ρ χ) = finrank k W * Nat.card (ClassSet Γ K₁) := by
  have hr : Γ.subtype.range = Γ := Subgroup.range_subtype Γ
  have : Finite (Formalism.L2.SG.ColsDim.Classes Γ.subtype K₁) := by
    show Finite (ClassSet Γ.subtype.range K₁)
    rw [hr]; exact hfin
  have := (Formalism.L2.SG.ColsDim.equi_dim Γ.subtype K₁ hst ρ χ).2
  rw [Formalism.L2.SG.ColsDim.equi_subtype] at this
  rw [this]
  show finrank k W * Nat.card (ClassSet Γ.subtype.range K₁) = _
  rw [hr]
end PI.UnitaryGroupMassFormula.DiaFixDim.Main
