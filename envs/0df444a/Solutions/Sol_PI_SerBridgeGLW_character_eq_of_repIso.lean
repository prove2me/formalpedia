-- Prove2me | solution 1 for PI.SerBridgeGLW.character_eq_of_repIso
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T10:21:41.293219+00:00
-- url     : https://prove2.me/submissions/335cca0b-17b9-4671-9d4f-72722a4b69cc

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IrreducibleCharacterSeries_IrrCharIff
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IrreducibleCharacterSeries_CharacterEqOfRepIso

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Polynomial CategoryTheory Formalism.IrreducibleCountingLemmas.TYPES Formalism.L2.NT
open PI PI.SerBridgeGLW
variable {G : Type} [Group G] [Fintype G]
namespace PI.SerBridgeGLW
theorem _root_.solution {V W : FDRep ℂ G} (h : RepIso V.ρ W.ρ) : V.character = W.character := by
  obtain ⟨e, he⟩ := h
  funext γ
  show LinearMap.trace ℂ V (V.ρ γ) = LinearMap.trace ℂ W (W.ρ γ)
  have hc : W.ρ γ = e.conj (V.ρ γ) := by
    ext w
    have h1 := he γ (e.symm w)
    rw [LinearEquiv.apply_symm_apply] at h1
    rw [LinearEquiv.conj_apply, LinearMap.comp_apply, LinearMap.comp_apply]
    exact h1.symm
  rw [hc, LinearMap.trace_conj']
end PI.SerBridgeGLW
