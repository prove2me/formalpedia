-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.DiaFixDim.Main.card_classes
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T11:01:40.834726+00:00
-- url     : https://prove2.me/submissions/2761b805-84dd-40af-9d4f-f35068007ef8

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_SiegelMassRatios_ClassAct
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_SiegelMassRatios_ColsDim
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FixedDimensionCount_ExistsSemidirectDecomposition
import Theorems.Thm_PI_UnitaryGroupMassFormula_DiaFixDim_Main_phiMap_inj
import Theorems.Thm_PI_UnitaryGroupMassFormula_DiaFixDim_Main_phiMap_surj

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
theorem _root_.solution {G : Type} [Group G] (Γ K K₀ D : Subgroup G) (hN : Normalises D K)
    (hK : K ≤ K₀) (hD : D ≤ K₀) (hn : IsNeat Γ K₀) :
    Nat.card (ClassSet Γ K) = Nat.card (ClassSet Γ (dk K D hN)) * K.relIndex D := by
  rw [← Nat.card_congr (Equiv.ofBijective (phiMap Γ K D hN)
    ⟨phiMap_inj Γ K K₀ D hN hK hD hn, phiMap_surj Γ K D hN⟩), Nat.card_prod,
    Subgroup.relIndex, Subgroup.index_eq_card]
end PI.UnitaryGroupMassFormula.DiaFixDim.Main
