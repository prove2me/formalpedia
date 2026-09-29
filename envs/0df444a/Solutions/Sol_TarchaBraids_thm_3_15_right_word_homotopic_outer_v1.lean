-- Prove2me | solution 1 for TarchaBraids.thm_3_15_right_word_homotopic_outer_v1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-21T13:23:56.763615+00:00
-- url     : https://prove2.me/submissions/fe249916-dfff-46d7-a472-9ee4e3a02bd1

import Mathlib
import Definitions.Def_TarchaBraids_right_interp_config_data_v1
import Definitions.Def_TarchaBraids_adjacent_word_loops_v1
import Definitions.Def_TarchaBraids_adjacent_outer_loop_v1
import Theorems.Thm_TarchaBraids_thm_3_15_right_interp_config_continuous_v1
import Theorems.Thm_TarchaBraids_thm_3_15_right_interp_boundaries_v1
import Theorems.Thm_TarchaBraids_thm_3_15_right_word_identification_v1

namespace TarchaBraids

open BraidsLinksMCG

lemma rightWordOuter_hi2_v1 {n : ℕ} (i j : Fin (n - 1))
    (hji : (j : ℕ) = (i : ℕ) + 1) : (i : ℕ) + 2 < n := by
  have hj := j.isLt
  omega

end TarchaBraids

open BraidsLinksMCG TarchaBraids

theorem solution :
    ∀ {n : ℕ} (i j : Fin (n - 1)) (hji : (j : ℕ) = (i : ℕ) + 1),
      Path.Homotopic (rightBraidWordLoop n i j) (outerRotateLoop i j hji) := by
  intro n i j hji
  have hC := thm_3_15_right_interp_config_continuous_v1 i j hji
  have hB := thm_3_15_right_interp_boundaries_v1 i j hji
  have hW := thm_3_15_right_word_identification_v1 (n := n) i j
  let H : Path.Homotopy (rightBraidWordLoop n i j) (outerRotateLoop i j hji) :=
    { toFun := fun z => configProj n (rightOuterInterpConfig i j hji z.1 z.2)
      continuous_toFun := (configProj n).continuous.comp hC
      map_zero_left := by
        intro q
        change configProj n (rightOuterInterpConfig i j hji 0 q) =
          rightBraidWordLoop n i j q
        rw [hB.1 q, hW q]
      map_one_left := by
        intro q
        have hi2 := rightWordOuter_hi2_v1 i j hji
        change configProj n (rightOuterInterpConfig i j hji 1 q) =
          outerRotateLoop i j hji q
        rw [hB.2.1 hi2 q]
        rfl
      prop' := by
        intro u q hq
        rcases hq with hq | hq
        · subst q
          change configProj n (rightOuterInterpConfig i j hji u 0) =
            rightBraidWordLoop n i j 0
          rw [hB.2.2.1 u]
          exact (rightBraidWordLoop n i j).source.symm
        · rw [Set.mem_singleton_iff] at hq
          subst q
          change configProj n (rightOuterInterpConfig i j hji u 1) =
            rightBraidWordLoop n i j 1
          rw [hB.2.2.2 u]
          exact (rightBraidWordLoop n i j).target.symm }
  exact ⟨H⟩
