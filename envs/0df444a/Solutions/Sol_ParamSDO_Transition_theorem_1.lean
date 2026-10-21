-- Prove2me | solution 1 for ParamSDO.Transition.theorem_1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-20T14:20:48.569997+00:00
-- url     : https://prove2.me/submissions/c48fa6e8-1836-4361-be2f-729544146494
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_ParamSDO_Transition_Setting
import Theorems.Thm_ParamSDO_Transition_transition_iff_frontier
import Theorems.Thm_ParamSDO_Transition_Srank_semialgebraic
import Theorems.Thm_ParamSDO_Transition_semialgebraic_frontier_finite

open ParamSDO.Transition

theorem solution {n m : ℕ} (A : Fin m → Matrix (Fin n) (Fin n) ℝ) (b : Fin m → ℝ)
    (C Cbar : Matrix (Fin n) (Fin n) ℝ)
    (hA : ∀ i, (A i).IsHermitian) (hC : C.IsHermitian) (hCbar : Cbar.IsHermitian)
    (h1 : Assumption1 A) (h2 : Assumption2 A b C Cbar) :
    {ϵbar : ℝ | IsTransitionPoint A b C Cbar ϵbar}.Finite := by
  have hfin : (⋃ (θ : Fin (n + 1)) (σ : Fin (n + 1)),
      frontier (Srank A b C Cbar θ σ)).Finite :=
    Set.finite_iUnion fun θ => Set.finite_iUnion fun σ =>
      semialgebraic_frontier_finite _
        (Srank_semialgebraic A b C Cbar hA hC hCbar h1 h2 θ σ)
  refine hfin.subset fun ϵbar hϵ => ?_
  obtain ⟨θ, σ, hθσ, hfr, -⟩ :=
    (transition_iff_frontier A b C Cbar hA hC hCbar h1 h2 ϵbar).1 hϵ
  simp only [Set.mem_iUnion]
  exact ⟨⟨θ, by omega⟩, ⟨σ, by omega⟩, hfr⟩
