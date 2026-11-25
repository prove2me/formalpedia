-- Prove2me | solution 1 for PositivityTheory.ThKEst.CS.Dual.separates
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T12:00:06.251931+00:00
-- url     : https://prove2.me/submissions/cbdc48e5-2afd-4a14-9d97-d35be5e9472b

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
omit [IsTopologicalAddGroup G]
namespace PositivityTheory.ThKEst.CS
namespace Dual
theorem _root_.solution (h : Dual r e) : (Achar h).SeparatesPoints := by
  intro q q' hqq'
  obtain ⟨x, rfl⟩ := QuotientAddGroup.mk_surjective q
  obtain ⟨x', rfl⟩ := QuotientAddGroup.mk_surjective q'
  obtain ⟨ξ, hξ⟩ : ∃ ξ, e ξ (-x + x') ≠ 1 := by
    by_contra h'
    push Not at h'
    exact hqq' (QuotientAddGroup.eq.2 (h.sep _ h'))
  refine ⟨chiC h ξ, ⟨chiC h ξ, Submodule.subset_span ⟨ξ, rfl⟩, rfl⟩, fun heq => hξ ?_⟩
  have h1 : e ξ x = e ξ x' := heq
  have h2 := h.addr ξ x (-x + x')
  rw [show x + (-x + x') = x' by abel, ← h1] at h2
  exact (mul_eq_left₀ (h.ne ξ x)).1 h2.symm
end Dual
end PositivityTheory.ThKEst.CS
