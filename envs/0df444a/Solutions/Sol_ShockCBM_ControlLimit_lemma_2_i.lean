-- Prove2me | solution 1 for ShockCBM.ControlLimit.lemma_2_i
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-31T00:42:29.106554+00:00
-- url     : https://prove2.me/submissions/5d559468-b607-4067-b15a-b6b72b8befcd
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_ShockCBM_ControlLimit_NEF
import Definitions.Def_ShockCBM_ControlLimit_Setting
import Theorems.Thm_ShockCBM_ControlLimit_rhs19_antitone_t
import Theorems.Thm_ShockCBM_ControlLimit_display_10

open ShockCBM.ControlLimit

theorem solution (M : Model) (hM : M.Standing) (x n t t' : ℕ) (htt : t ≤ t') :
    M.V (x, n, t') ≤ M.V (x, n, t) := by
  have hB := (display_10 M hM).2.1
  have hE := rhs19_antitone_t M hM x n t t' htt
  rw [hB (x, n, t'), hB (x, n, t)]
  unfold Model.bellman
  dsimp only
  split_ifs
  · exact le_rfl
  · exact min_le_min le_rfl (mul_le_mul_of_nonneg_left hE hM.γ_pos.le)
