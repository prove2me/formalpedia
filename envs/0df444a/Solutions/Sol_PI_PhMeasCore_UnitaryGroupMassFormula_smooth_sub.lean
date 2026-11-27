-- Prove2me | solution 1 for PI.PhMeasCore.UnitaryGroupMassFormula.smooth_sub
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-27T05:16:52.946588+00:00
-- url     : https://prove2.me/submissions/f6b1f0d7-bb5a-4359-89bc-0a5b90a1bc8f

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SmoothTranslationMeasure_ContDiffMulRight
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SmoothTranslationMeasure_SmoothTranslate

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
open scoped ContDiff
noncomputable section
open PI PI.PhMeasCore PI.PhMeasCore.UnitaryGroupMassFormula
open PI.PhMeasCore
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {n : ℕ} {Hm : Matrix (Fin n) (Fin n) ℂ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)}
namespace PI.PhMeasCore.UnitaryGroupMassFormula
theorem _root_.solution {v v' : H} (hv : v ∈ smoothVecs Hm σ) (hv' : v' ∈ smoothVecs Hm σ) :
    v - v' ∈ smoothVecs Hm σ := by
  have h₁ : PI.PhMeasCore.SmoothOnH Hm (fun x => σ x v) := hv
  have h₂ : PI.PhMeasCore.SmoothOnH Hm (fun x => σ x v') := hv'
  show PI.PhMeasCore.SmoothOnH Hm (fun x => σ x (v - v'))
  intro g₀ hg₀
  obtain ⟨U₁, F₁, hU₁, m₁, hF₁, e₁⟩ := h₁ g₀ hg₀
  obtain ⟨U₂, F₂, hU₂, m₂, hF₂, e₂⟩ := h₂ g₀ hg₀
  refine ⟨U₁ ∩ U₂, fun x => F₁ x - F₂ x, hU₁.inter hU₂, ⟨m₁, m₂⟩, ?_, ?_⟩
  · exact (hF₁.mono Set.inter_subset_left).sub (hF₂.mono Set.inter_subset_right)
  · intro x hx hxI
    have a₁ : σ x v = F₁ x := e₁ x hx.1 hxI
    have a₂ : σ x v' = F₂ x := e₂ x hx.2 hxI
    show σ x (v - v') = F₁ x - F₂ x
    rw [map_sub, a₁, a₂]
end PI.PhMeasCore.UnitaryGroupMassFormula
