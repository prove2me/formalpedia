-- Prove2me | solution 1 for PI.SerBridgeGLW.mem_inv_linHom_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T10:22:17.217113+00:00
-- url     : https://prove2.me/submissions/6a6e13ee-fda1-4d94-bffa-00dcb137310c

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IrreducibleCharacterSeries_IrrCharIff
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IrreducibleCharacterSeries_ConjugateCharacterFormula
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IrreducibleCharacterSeries_FrobeniusSumFormula
import Theorems.Thm_Formalism_FrobeniusOrbits_galEquiv_apply
import Theorems.Thm_Formalism_L2_Host_restr_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.FrobeniusOrbits.galEquiv_apply
attribute [local simp] Formalism.L2.Host.restr_apply



set_option autoImplicit false
noncomputable section
open CategoryTheory Formalism.IrreducibleCountingLemmas.TYPES
open PI PI.SerBridgeGLW
namespace PI.SerBridgeGLW
theorem _root_.solution {G V W : Type} [Group G] [AddCommGroup V] [Module ℂ V] [AddCommGroup W]
    [Module ℂ W] (ρV : Representation ℂ G V) (ρW : Representation ℂ G W) (f : V →ₗ[ℂ] W) :
    f ∈ (Representation.linHom ρV ρW).invariants ↔ ∀ g, f ∘ₗ ρV g = ρW g ∘ₗ f := by
  rw [Representation.mem_invariants]
  constructor
  · intro h g
    ext x
    have := congrArg (fun φ : V →ₗ[ℂ] W => φ (ρV g x)) (h g)
    simp only [Representation.linHom_apply, LinearMap.comp_apply, Representation.inv_self_apply] at this
    simp only [LinearMap.comp_apply]
    exact this.symm
  · intro h g
    ext x
    have := congrArg (fun φ : V →ₗ[ℂ] W => φ (ρV g⁻¹ x)) (h g)
    simp only [LinearMap.comp_apply, Representation.self_inv_apply] at this
    simp only [Representation.linHom_apply, LinearMap.comp_apply]
    exact this.symm
end PI.SerBridgeGLW
