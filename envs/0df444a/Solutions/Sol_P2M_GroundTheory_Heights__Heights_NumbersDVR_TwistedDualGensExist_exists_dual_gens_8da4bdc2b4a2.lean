-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_NumbersDVR_TwistedDualGensExist_exists_dual_gens_8da4bdc2b4a2
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T05:25:25.812606+00:00
-- url     : https://prove2.me/submissions/e7fedc10-2784-48db-899f-fb4f48f12194

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsTwistedDualGensExist
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PTwistedDualGensExist
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_TwistedDualGensExist_dualSub_fg_6e089a7ed252

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.NumbersDVR
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo
noncomputable section
variable {O : Type*} [CommRing O] {Ω : Type*} [Field Ω] [Algebra O Ω] {τ : Type*}
  {r : ℕ} {E : Type*} [AddCommGroup E] [Module Ω E]
namespace GroundTheory.Heights₂.Heights.NumbersDVR
namespace TwistedDualGensExist
theorem _root_.solution [IsNoetherianRing O] [Fintype τ] {x : τ → Ω}
    (B : ChartBundle O x r E) {c : τ} (hc : x c ≠ 0) :
    ∃ S : Finset (Module.Dual Ω E), (∀ ψ ∈ S, ∀ v ∈ B.lat c, ψ v ∈ chartRing O x c) ∧
      ∀ ψ' : Module.Dual Ω E, (∀ v ∈ B.lat c, ψ' v ∈ chartRing O x c) →
        ∃ u : Module.Dual Ω E → Ω, (∀ ψ, u ψ ∈ chartRing O x c) ∧ ∑ ψ ∈ S, u ψ • ψ = ψ' := by
  obtain ⟨S, hS⟩ := TwistedDualGensExist.dualSub_fg B hc
  refine ⟨S, fun ψ hψ => ?_, fun ψ' hψ' => ?_⟩
  · have : ψ ∈ TwistedDualGensExist.dualSub B c := hS ▸ Submodule.subset_span hψ
    exact this
  · have h : ψ' ∈ Submodule.span (chartRing O x c) (S : Set (Module.Dual Ω E)) := by
      rw [hS]
      exact hψ'
    obtain ⟨u, -, hu⟩ := Submodule.mem_span_finset.1 h
    exact ⟨fun ψ => u ψ, fun ψ => (u ψ).2, hu⟩
end TwistedDualGensExist
end GroundTheory.Heights₂.Heights.NumbersDVR
