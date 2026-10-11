-- Prove2me | solution 1 for TensorNP.Rank.rankQ_tensorA_gt_two
-- status  : ACCEPTED   (prove)
-- author  : @arexychen
-- created : 2026-10-11T03:52:25.626122+00:00
-- url     : https://prove2.me/submissions/aceec98d-9db1-4392-a270-e84c9eb2bec9

import Definitions.Def_TensorNP_Rank_Defs
import Definitions.Def_TensorNP_Rank_Construction
import Theorems.Thm_TensorNP_Rank_eq29_iff_system30
import Theorems.Thm_TensorNP_Rank_lemma_8_1
import Mathlib

open TensorNP.Rank

theorem solution : 2 < rankOver ℚ tensorA := by
  by_contra h
  obtain ⟨u₁, v₁, u₂, v₂, u₃, v₃, hA⟩ :=
    eq29_iff_system30.1 tensorA (Nat.le_of_not_gt h)
  apply lemma_8_1
  refine ⟨u₁ 0, u₂ 0, u₃ 0, u₁ 1, u₂ 1, u₃ 1,
    v₁ 0, v₂ 0, v₃ 0, v₁ 1, v₂ 1, v₃ 1, ?_⟩
  exact (eq29_iff_system30.2 u₁ u₂ u₃ v₁ v₂ v₃).mp (by simpa using hA)
