-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Inter_finsum_mem_eq_sum_of_injective_7f5c6e678458
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T03:26:31.337194+00:00
-- url     : https://prove2.me/submissions/a6df487e-9fe1-4600-a419-2991f08a223f

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_LocQuotCard

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Inter
namespace GroundTheory.Heights₂.Heights.Inter
theorem _root_.solution {α β : Type*} [Fintype β] (s : Set α) (f : α → ℝ) (g : β → α)
    (hg : Function.Injective g) (hs : ∀ x, g x ∈ s) (hf : ∀ a ∈ s, f a ≠ 0 → a ∈ Set.range g) :
    ∑ᶠ a ∈ s, f a = ∑ x, f (g x) := by
  have hS : s ∩ Function.support f = Set.range g ∩ Function.support f := by
    ext a
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨hf a h1 h2, h2⟩
    · rintro ⟨⟨x, rfl⟩, h2⟩
      exact ⟨hs x, h2⟩
  rw [← finsum_mem_inter_support, hS, finsum_mem_inter_support, finsum_mem_range hg, finsum_eq_sum_of_fintype]
end GroundTheory.Heights₂.Heights.Inter
