-- Prove2me | solution 1 for TensorNP.Rank.theorem_1_14
-- status  : ACCEPTED   (prove)
-- author  : @arexychen
-- created : 2026-10-11T03:54:25.993501+00:00
-- url     : https://prove2.me/submissions/79f5928d-5e7a-4238-8b40-70335e93d7a9

import Definitions.Def_TensorNP_Rank_Defs
import Definitions.Def_TensorNP_Rank_Construction
import Theorems.Thm_TensorNP_Rank_real_decomposition
import Theorems.Thm_TensorNP_Rank_eq29_iff_system30
import Theorems.Thm_TensorNP_Rank_lemma_8_1
import Mathlib

open TensorNP.Rank

theorem solution :
    ∃ A : Fin 2 → Fin 2 → Fin 2 → ℚ,
      rankOver ℝ (fun i j k => (A i j k : ℝ)) < rankOver ℚ A := by
  have hq : 2 < rankOver ℚ tensorA := by
    by_contra h
    obtain ⟨u₁, v₁, u₂, v₂, u₃, v₃, hA⟩ :=
      eq29_iff_system30.1 tensorA (Nat.le_of_not_gt h)
    apply lemma_8_1
    refine ⟨u₁ 0, u₂ 0, u₃ 0, u₁ 1, u₂ 1, u₃ 1,
      v₁ 0, v₂ 0, v₃ 0, v₁ 1, v₂ 1, v₃ 1, ?_⟩
    exact (eq29_iff_system30.2 u₁ u₂ u₃ v₁ v₂ v₃).mp (by simpa using hA)
  exact ⟨tensorA, lt_of_le_of_lt real_decomposition.2 hq⟩
