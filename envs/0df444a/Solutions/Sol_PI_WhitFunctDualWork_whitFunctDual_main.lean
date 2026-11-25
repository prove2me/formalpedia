-- Prove2me | solution 1 for PI.WhitFunctDualWork.whitFunctDual_main
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T11:37:42.358977+00:00
-- url     : https://prove2.me/submissions/da138539-c661-4940-8c7c-a98a89f37ba4

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_WhitFunctDual
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WhittakerFunctionalDual_StableOfIrreducible
import Theorems.Thm_PI_WhitFunctDualWork_isIrr_dual
import Theorems.Thm_PI_WhitFunctDualWork_whit_mem

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PI PI.WhitFunctDualWork
open Formalism.L2.SG.GGMirabolic
namespace PI.WhitFunctDualWork
theorem _root_.solution : PI.WhitFunctDual := by
  intro hGG F _ _ k ψ₀ hψ V _ _ _ π hπ ℓ₁ ℓ₂ h1 h2 hne
  have hψ' : ψ₀⁻¹ ≠ 1 := inv_ne_one.mpr hψ
  have hirr := isIrr_dual π hπ
  have hdim := hGG F (Module.Dual ℂ V) k ψ₀⁻¹ (Representation.dual π) hψ' hirr
  have m1 : ℓ₁ ∈ Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.besselSpace (Representation.dual π) ψ₀⁻¹ 0 0 := whit_mem ψ₀ π ℓ₁ h1
  have m2 : ℓ₂ ∈ Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.besselSpace (Representation.dual π) ψ₀⁻¹ 0 0 := whit_mem ψ₀ π ℓ₂ h2
  have hne' : (⟨ℓ₁, m1⟩ : Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.besselSpace (Representation.dual π) ψ₀⁻¹ 0 0) ≠ 0 :=
    fun h0 => hne (congrArg Subtype.val h0)
  have hpos : 0 < Module.finrank ℂ (Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.besselSpace (Representation.dual π) ψ₀⁻¹ 0 0) :=
    Module.finrank_pos_iff_exists_ne_zero.mpr ⟨_, hne'⟩
  obtain ⟨c, hc⟩ := (finrank_eq_one_iff_of_nonzero' _ hne').mp (le_antisymm hdim hpos) ⟨ℓ₂, m2⟩
  exact ⟨c, (congrArg Subtype.val hc).symm⟩
end PI.WhitFunctDualWork
