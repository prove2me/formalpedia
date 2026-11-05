-- Prove2me | solution 1 for QualityEncroach.Differ.proposition_4_ii
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-05T04:40:06.137683+00:00
-- url     : https://prove2.me/submissions/68e1fcb6-bf50-4234-ab4a-f12ffde02c3f
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_QualityEncroach_Differ_Game
import Theorems.Thm_QualityEncroach_Differ_proposition_3
import Theorems.Thm_QualityEncroach_Differ_proposition_1_iii
import Theorems.Thm_QualityEncroach_Differ_proposition_4_ii_differentiated

open QualityEncroach.Differ

theorem solution (k c : ℝ) (hk : 0 < k) (hc : 0 ≤ c) (σ : Profile)
    (hσ : IsSPE k c (Set.Ioi 0) σ) (henc : 0 < σ.path.qM) :
    1 / (54 * k) < mfrPayoff k c σ.path ∧ retailerPayoff σ.path < 1 / (108 * k) := by
  have ht : σ.t ≤ 1 := proposition_3 k c hk hc σ hσ henc
  rcases lt_or_eq_of_le ht with hlt | heq
  · exact proposition_4_ii_differentiated k c hk hc σ hσ henc hlt
  · -- with `t = 1` the profile is an SPE of the uniform-quality game
    have hU : IsSPE k c {1} σ := by
      obtain ⟨h3, h2, hu, _, h1⟩ := hσ
      refine ⟨?_, ?_, hu, heq, ?_⟩
      · intro w u t qR hu' ht' hqR
        exact h3 w u t qR hu' (by rw [Set.mem_singleton_iff.mp ht']; norm_num) hqR
      · intro w u t hu' ht'
        exact h2 w u t hu' (by rw [Set.mem_singleton_iff.mp ht']; norm_num)
      · intro w u t hu' ht'
        exact h1 w u t hu' (by rw [Set.mem_singleton_iff.mp ht']; norm_num)
    exact proposition_1_iii k c hk hc σ hU henc
