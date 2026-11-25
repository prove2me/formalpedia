-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.DiaFixDim.Main.fixAt_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T10:56:38.873257+00:00
-- url     : https://prove2.me/submissions/c230d66c-7152-4a2c-9bb5-0725ca0885b8

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_SiegelMassRatios_ClassAct
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_SiegelMassRatios_ColsDim
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FixedDimensionCount_ExistsSemidirectDecomposition
import Theorems.Thm_PI_UnitaryGroupMassFormula_DiaFixDim_Main_le_dk
import Theorems.Thm_PI_UnitaryGroupMassFormula_DiaFixDim_Main_D_le_dk
import Theorems.Thm_PI_UnitaryGroupMassFormula_DiaFixDim_Main_mem_AMFChi
import Theorems.Thm_Formalism_L2_SG_ClassAct_mem_FixAt


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
    [Module k W] (Γ K D : Subgroup G) (hN : Normalises D K) (ρ : Representation k Γ W)
    (χ : K →* kˣ) (hinv : ∀ δ ∈ D, ∀ κ κ' : K, (κ' : G) = δ * κ * δ⁻¹ → χ κ' = χ κ)
    (htriv : ∀ κ : K, (κ : G) ∈ D → χ κ = 1) :
    FixAt k Γ K ρ χ D = AMFChi k Γ (dk K D hN) ρ (chi1 hN k χ hinv htriv) := by
  ext f
  rw [mem_FixAt, mem_AMFChi, mem_AMFChi]
  constructor
  · rintro ⟨hA, hD⟩ γ g κ₁
    obtain ⟨δ, hδ, κ, hκ, e⟩ := (mem_dk K D hN).1 κ₁.2
    have hc : chi1 hN k χ hinv htriv κ₁ = χ ⟨κ, hκ⟩ := chi1Fun_eq k χ htriv κ₁ hδ ⟨κ, hκ⟩ e
    rw [hc, e, show (γ : G) * g * (δ * κ) = (γ : G) * (g * δ) * κ by group]
    rw [hA γ (g * δ) ⟨κ, hκ⟩, hD δ hδ g]
  · intro h
    refine ⟨fun γ g κ => ?_, fun δ hδ g => ?_⟩
    · have hc : chi1 hN k χ hinv htriv ⟨κ, le_dk K D hN κ.2⟩ = χ κ :=
        chi1Fun_eq k χ htriv _ D.one_mem κ (by simp)
      have := h γ g ⟨κ, le_dk K D hN κ.2⟩
      rw [hc] at this
      exact this
    · have hc : chi1 hN k χ hinv htriv ⟨δ, D_le_dk K D hN hδ⟩ = 1 :=
        (chi1Fun_eq k χ htriv _ hδ 1 (by simp)).trans (map_one χ)
      have := h 1 g ⟨δ, D_le_dk K D hN hδ⟩
      rw [hc] at this
      simpa using this
end PI.UnitaryGroupMassFormula.DiaFixDim.Main
