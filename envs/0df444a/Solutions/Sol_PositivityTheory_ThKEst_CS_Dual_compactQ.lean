-- Prove2me | solution 1 for PositivityTheory.ThKEst.CS.Dual.compactQ
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T11:59:58.318366+00:00
-- url     : https://prove2.me/submissions/b4f2d032-fba5-4569-9116-8d834958b967

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
theorem _root_.solution (h : Dual r e) : CompactSpace (G ⧸ r.range) := by
  obtain ⟨K, hK, hKc⟩ := h.cpt
  refine ⟨?_⟩
  have h : (Set.univ : Set (G ⧸ r.range)) = (QuotientAddGroup.mk : G → G ⧸ r.range) '' K := by
    ext q
    simp only [Set.mem_univ, Set.mem_image, true_iff]
    obtain ⟨z, rfl⟩ := QuotientAddGroup.mk_surjective q
    obtain ⟨ξ, hξ⟩ := hKc z
    refine ⟨z - r ξ, hξ, ?_⟩
    rw [QuotientAddGroup.eq, show -(z - r ξ) + z = r ξ by abel]
    exact ⟨ξ, rfl⟩
  rw [h]
  exact hK.image continuous_quotient_mk'
end Dual
end PositivityTheory.ThKEst.CS
