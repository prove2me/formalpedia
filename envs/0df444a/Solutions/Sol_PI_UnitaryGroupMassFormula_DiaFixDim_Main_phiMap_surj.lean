-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.DiaFixDim.Main.phiMap_surj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T10:45:10.454494+00:00
-- url     : https://prove2.me/submissions/fdb41efa-b89b-4f14-b845-83a07939e131

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
theorem _root_.solution {G : Type} [Group G] (Γ K D : Subgroup G) (hN : Normalises D K) :
    Function.Surjective (phiMap Γ K D hN) := by
  intro c
  obtain ⟨γ, hγ, κ₁, hκ₁, e⟩ := (DoubleCoset.eq Γ (dk K D hN)
    (Quotient.out (DoubleCoset.mk Γ (dk K D hN) (Quotient.out c))) (Quotient.out c)).1
    (DoubleCoset.out_eq' Γ (dk K D hN) (DoubleCoset.mk Γ (dk K D hN) (Quotient.out c)))
  obtain ⟨δ, hδ, κ, hκ, rfl⟩ := (mem_dk K D hN).1 hκ₁
  obtain ⟨h, hh⟩ := QuotientGroup.mk_out_eq_mul (K.subgroupOf D) (⟨δ, hδ⟩ : D)
  refine ⟨(DoubleCoset.mk Γ (dk K D hN) (Quotient.out c),
    (QuotientGroup.mk (⟨δ, hδ⟩ : D) : D ⧸ K.subgroupOf D)), ?_⟩
  refine Eq.trans ?_ (DoubleCoset.out_eq' Γ K c)
  dsimp only [phiMap]
  rw [hh]
  have hcoe : (((⟨δ, hδ⟩ : D) * (h : D) : D) : G) = δ * ((h : D) : G) := rfl
  rw [hcoe]
  refine (DoubleCoset.eq Γ K _ _).2 ⟨γ, hγ, ((h : D) : G)⁻¹ * κ,
    K.mul_mem (K.inv_mem (Subgroup.mem_subgroupOf.1 h.2)) hκ, ?_⟩
  refine e.trans ?_
  group
end PI.UnitaryGroupMassFormula.DiaFixDim.Main
