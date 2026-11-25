-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.DiaFixDim.Main.phiMap_inj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T10:40:04.78322+00:00
-- url     : https://prove2.me/submissions/5951af99-caef-4955-9f9c-e2402e713c9f

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
theorem _root_.solution {G : Type} [Group G] (Γ K K₀ D : Subgroup G) (hN : Normalises D K)
    (hK : K ≤ K₀) (hD : D ≤ K₀) (hn : IsNeat Γ K₀) : Function.Injective (phiMap Γ K D hN) := by
  rintro ⟨c, q⟩ ⟨c', q'⟩ he
  obtain ⟨γ, hγ, κ, hκ, e0⟩ := (DoubleCoset.eq Γ K _ _).1 he
  have e : Quotient.out c' * ((Quotient.out q' : D) : G) =
      γ * (Quotient.out c * ((Quotient.out q : D) : G)) * κ := e0
  have hc : c = c' := by
    rw [← DoubleCoset.out_eq' Γ (dk K D hN) c, ← DoubleCoset.out_eq' Γ (dk K D hN) c']
    refine (DoubleCoset.eq Γ (dk K D hN) _ _).2 ⟨γ, hγ,
      ((Quotient.out q : D) : G) * κ * ((Quotient.out q' : D) : G)⁻¹, ?_, ?_⟩
    · exact (mem_dk K D hN).2 ⟨((Quotient.out q : D) : G) * ((Quotient.out q' : D) : G)⁻¹,
        D.mul_mem (Quotient.out q).2 (D.inv_mem (Quotient.out q').2),
        ((Quotient.out q' : D) : G) * κ * ((Quotient.out q' : D) : G)⁻¹,
        hN _ (Quotient.out q').2 _ hκ, by group⟩
    · calc Quotient.out c' = Quotient.out c' * ((Quotient.out q' : D) : G) *
            ((Quotient.out q' : D) : G)⁻¹ := by group
        _ = _ := by rw [e]; group
  rw [← hc] at e
  have hγe : γ = Quotient.out c * ((Quotient.out q' : D) : G) * κ⁻¹ *
      ((Quotient.out q : D) : G)⁻¹ * (Quotient.out c)⁻¹ := by
    rw [e]; group
  have hγ1 : γ = 1 := by
    refine neat_one hn hγ (x := Quotient.out c) ?_
    have h3 : (Quotient.out c)⁻¹ * γ * Quotient.out c =
        ((Quotient.out q' : D) : G) * κ⁻¹ * ((Quotient.out q : D) : G)⁻¹ := by
      rw [hγe]; group
    rw [h3]
    exact K₀.mul_mem (K₀.mul_mem (hD (Quotient.out q').2) (K₀.inv_mem (hK hκ)))
      (K₀.inv_mem (hD (Quotient.out q).2))
  have e3 : Quotient.out c * ((Quotient.out q' : D) : G) =
      Quotient.out c * (((Quotient.out q : D) : G) * κ) := by
    rw [e, hγ1]; group
  have hq : q = q' := by
    rw [← QuotientGroup.out_eq' q, ← QuotientGroup.out_eq' q', QuotientGroup.eq,
      Subgroup.mem_subgroupOf]
    have h4 : (((Quotient.out q)⁻¹ * Quotient.out q' : D) : G) = κ := by
      rw [Subgroup.coe_mul, Subgroup.coe_inv, mul_left_cancel e3]; group
    rw [h4]; exact hκ
  rw [hc, hq]
end PI.UnitaryGroupMassFormula.DiaFixDim.Main
