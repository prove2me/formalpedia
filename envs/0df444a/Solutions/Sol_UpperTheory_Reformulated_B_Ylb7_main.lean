-- Prove2me | solution 1 for UpperTheory.Reformulated.B.Ylb7.main
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-27T05:34:30.169661+00:00
-- url     : https://prove2.me/submissions/99b8a51a-3d0f-44ae-baa4-b78217a84290

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_ImportsSideTail

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

namespace UpperTheory.Reformulated.B.Ylb7
theorem _root_.solution :
    ∀ {G : Type} [inst : Group G] [inst_1 : TopologicalSpace G] {C : Set G},
      IsCompact C →
        ∀ {n : Set (G × G)}, IsOpen n → (∀ c ∈ C, (c, (1 : G)) ∈ n) → ∃ O ∈ nhds (1 : G), ∀ c ∈ C, ∀ u ∈ O, (c, u) ∈ n := by
  intro G _ _ C hC n hn h
  have hsub : C ×ˢ ({1} : Set G) ⊆ n := by
    rintro ⟨c, u⟩ ⟨hc, hu⟩
    simp only [Set.mem_singleton_iff] at hu
    subst hu
    exact h c hc
  obtain ⟨U, V, _, hV, _, hV1, hUV⟩ := generalized_tube_lemma hC isCompact_singleton hn hsub
  refine ⟨V, hV.mem_nhds (hV1 rfl), ?_⟩
  intro c hc u hu
  exact hUV ⟨‹C ⊆ U› hc, hu⟩
end UpperTheory.Reformulated.B.Ylb7
