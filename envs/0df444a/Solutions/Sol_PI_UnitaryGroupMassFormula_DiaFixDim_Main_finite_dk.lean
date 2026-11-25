-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.DiaFixDim.Main.finite_dk
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T10:39:41.152694+00:00
-- url     : https://prove2.me/submissions/c4aa3ddb-c8fc-4b5f-ba7c-f94e24fa84ed

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_SiegelMassRatios_ClassAct
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_SiegelMassRatios_ColsDim
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FixedDimensionCount_ExistsSemidirectDecomposition
import Theorems.Thm_PI_UnitaryGroupMassFormula_DiaFixDim_Main_le_dk

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
theorem _root_.solution {G : Type} [Group G] (Γ K D : Subgroup G) (hN : Normalises D K)
    (hfin : Finite (ClassSet Γ K)) : Finite (ClassSet Γ (dk K D hN)) := by
  refine Finite.of_surjective
    (fun c : ClassSet Γ K => DoubleCoset.mk Γ (dk K D hN) (Quotient.out c)) ?_
  intro c₁
  refine ⟨DoubleCoset.mk Γ K (Quotient.out c₁), ?_⟩
  obtain ⟨γ, hγ, κ, hκ, e⟩ := (DoubleCoset.eq Γ K
    (Quotient.out (DoubleCoset.mk Γ K (Quotient.out c₁))) (Quotient.out c₁)).1
    (DoubleCoset.out_eq' Γ K (DoubleCoset.mk Γ K (Quotient.out c₁)))
  refine Eq.trans ?_ (DoubleCoset.out_eq' Γ (dk K D hN) c₁)
  show DoubleCoset.mk Γ (dk K D hN) (Quotient.out (DoubleCoset.mk Γ K (Quotient.out c₁))) = _
  exact (DoubleCoset.eq Γ (dk K D hN) _ _).2 ⟨γ, hγ, κ, le_dk K D hN hκ, e⟩
end PI.UnitaryGroupMassFormula.DiaFixDim.Main
