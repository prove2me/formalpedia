-- Prove2me | solution 1 for PI.UMultOne.GelfSpanWork.schur
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T10:43:14.154883+00:00
-- url     : https://prove2.me/submissions/0ed335e4-5128-451f-9ac4-de309e5ac21a

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UMultOne
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IntegralSpanAlgebra_Burnside
import Theorems.Thm_PI_UMultOne_GelfSpanWork_spanAlg_smul
import Theorems.Thm_PI_UMultOne_GelfSpanWork_spanAlg_simple

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.UMultOne PI.UMultOne.GelfSpanWork
open Matrix Module
variable {G : Type} [Group G] {N : ℕ}
namespace PI.UMultOne.GelfSpanWork
theorem _root_.solution (ρ : G →* GL (Fin N) ℂ) (hN : 0 < N) (hI : Irr ρ)
    (φ : (Fin N → ℂ) →ₗ[spanAlg ρ] (Fin N → ℂ)) : ∃ c : ℂ, ∀ v, φ v = c • v := by
  have := spanAlg_simple ρ hN hI
  have : Nonempty (Fin N) := ⟨⟨0, hN⟩⟩
  obtain ⟨c, hc⟩ := Module.End.exists_eigenvalue (φ.restrictScalars ℂ)
  obtain ⟨v, hv⟩ := hc.exists_hasEigenvector
  refine ⟨c, fun w => ?_⟩
  let K : Submodule (spanAlg ρ) (Fin N → ℂ) :=
    { carrier := {w | φ w = c • w}
      add_mem' := by
        intro a b ha hb
        simp only [Set.mem_ofPred_eq] at *
        rw [map_add, ha, hb, smul_add]
      zero_mem' := by simp
      smul_mem' := by
        intro a x hx
        simp only [Set.mem_ofPred_eq] at *
        rw [map_smul, hx, spanAlg_smul, spanAlg_smul, map_smul] }
  have hvK : v ∈ K := by
    have := hv.apply_eq_smul
    simpa [K] using this
  have hK : K = ⊤ := by
    rcases IsSimpleOrder.eq_bot_or_eq_top K with h | h
    · exfalso
      have : v ∈ (⊥ : Submodule (spanAlg ρ) (Fin N → ℂ)) := h ▸ hvK
      exact hv.2 ((Submodule.mem_bot _).mp this)
    · exact h
  have : w ∈ K := hK ▸ Submodule.mem_top
  exact this
end PI.UMultOne.GelfSpanWork
