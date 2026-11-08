-- Prove2me | solution 1 for StrongPerfectGraph.Main.perfect_iff_berge
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-07T06:15:28.833496+00:00
-- url     : https://prove2.me/submissions/b3959981-7289-4953-921f-ee7a152eb771
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Theorems.Thm_StrongPerfectGraph_Main_perfect_berge
import Theorems.Thm_StrongPerfectGraph_Main_basic_perfect
import Theorems.Thm_StrongPerfectGraph_Main_complement_perfect
import Theorems.Thm_StrongPerfectGraph_Main_minimum_imperfect_no_proper_two_join
import Theorems.Thm_StrongPerfectGraph_Main_minimum_imperfect_no_proper_homogeneous_pair
import Theorems.Thm_StrongPerfectGraph_Main_minimum_imperfect_no_balanced_skew_partition
import Theorems.Thm_StrongPerfectGraph_Main_berge_decomposition

open StrongPerfectGraph.Main

/-- The proof of 1.2 assuming 1.3 (p. 56): no minimum imperfect graph exists. -/
theorem spgt_no_minimum_imperfect {W : Type*} [Fintype W] [DecidableEq W] (H : SimpleGraph W) :
    ¬ IsMinimumImperfect H := by
    intro hH
    obtain ⟨hB, hP, hmin⟩ := hH
    have hHc : IsMinimumImperfect Hᶜ := by
      refine ⟨⟨hB.2, by simpa using hB.1⟩, fun h => hP ?_, hmin⟩
      simpa using complement_perfect Hᶜ h
    rcases berge_decomposition H hB with h | h | h | h | h
    · exact hP (basic_perfect H h)
    · exact minimum_imperfect_no_proper_two_join H ⟨hB, hP, hmin⟩ h
    · exact minimum_imperfect_no_proper_two_join Hᶜ hHc h
    · exact minimum_imperfect_no_proper_homogeneous_pair H ⟨hB, hP, hmin⟩ h
    · exact minimum_imperfect_no_balanced_skew_partition H ⟨hB, hP, hmin⟩ h
theorem solution {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) : IsPerfect G ↔ IsBerge G := by
  have hfin : ∀ n : ℕ, ∀ H : SimpleGraph (Fin n), IsBerge H → IsPerfect H := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro H hB
      by_contra hP
      exact spgt_no_minimum_imperfect H ⟨hB, hP, fun m hm H' hB' => ih m (by simpa using hm) H' hB'⟩
  refine ⟨perfect_berge G, fun hB => ?_⟩
  by_contra hP
  exact spgt_no_minimum_imperfect G ⟨hB, hP, fun m _ H' hB' => hfin m H' hB'⟩
