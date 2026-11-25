-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.AI.cone_preimage
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T12:27:31.991683+00:00
-- url     : https://prove2.me/submissions/b7b818f2-e494-45d9-93b1-33e6c72207c7

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_KappaSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_KappaA

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Set
open scoped Pointwise
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.AI
namespace ReciprocityTheory.ChartRestriction.G.AI
theorem _root_.solution (L : E3 ≃ₗᵢ[ℝ] E3) (s : Set S2) :
    Ioo (0 : ℝ) 1 • ((↑) '' ((fun n : S2 => (⟨L n, by simp⟩ : S2)) ⁻¹' s) : Set E3) =
      L ⁻¹' (Ioo (0 : ℝ) 1 • ((↑) '' s : Set E3)) := by
  ext x
  simp only [Set.mem_preimage, Set.mem_smul, Set.mem_image]
  constructor
  · rintro ⟨r, hr, _, ⟨n, hn, rfl⟩, rfl⟩
    exact ⟨r, hr, _, ⟨_, hn, rfl⟩, by simp⟩
  · rintro ⟨r, hr, _, ⟨m, hm, rfl⟩, hx⟩
    refine ⟨r, hr, _, ⟨⟨L.symm m, by simp⟩, ?_, rfl⟩, ?_⟩
    · convert hm using 1
      ext
      simp
    · apply L.injective
      rw [← hx]
      simp
end ReciprocityTheory.ChartRestriction.G.AI
