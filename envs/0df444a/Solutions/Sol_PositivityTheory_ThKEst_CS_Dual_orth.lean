-- Prove2me | solution 1 for PositivityTheory.ThKEst.CS.Dual.orth
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T12:00:02.822321+00:00
-- url     : https://prove2.me/submissions/c62dc0f7-fb91-4aeb-bfe9-fa153acdd838

import Mathlib
import Definitions.Def_Development_WeilBound_ThetaLifts_FrameEstimates_CoefSumA

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Topology Filter
open scoped ENNReal ComplexConjugate Pointwise
open PositivityTheory PositivityTheory.ThKEst PositivityTheory.ThKEst.CS
variable {G Γ : Type} [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G] [AddCommGroup Γ]
variable {r : Γ →+ G} {e : Γ → G → ℂ}
variable [MeasurableSpace G] [BorelSpace G] [Countable Γ] {μ : Measure G} [μ.IsAddHaarMeasure] {D : Set G}
namespace PositivityTheory.ThKEst.CS
namespace Dual
theorem _root_.solution (h : Dual r e) (hD : IsAddFundamentalDomain r.range D μ) {ξ : Γ} (hξ : ξ ≠ 0) :
    ∫ u in D, e ξ u ∂μ = 0 := by
  obtain ⟨u₀, hu₀⟩ := h.nondeg ξ hξ
  have hD' := hD.vadd_of_comm u₀
  have h1 := hD.setIntegral_eq hD' (f := e ξ) (fun g s => by
    obtain ⟨_, η, rfl⟩ := g
    exact h.per ξ η s)
  have h2 := (measurePreserving_add_left μ u₀).setIntegral_image_emb (measurableEmbedding_addLeft u₀) (e ξ) D
  have e' : u₀ +ᵥ D = (fun s => u₀ + s) '' D := rfl
  rw [e', h2] at h1
  simp only [h.addr] at h1
  rw [integral_const_mul] at h1
  by_contra hne
  exact hu₀ ((mul_eq_right₀ hne).1 h1.symm)
end Dual
end PositivityTheory.ThKEst.CS
