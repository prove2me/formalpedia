-- Prove2me | solution 1 for PolyhedralSOC.Sandwich.feas_subset_feasRelaxed
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-09-27T22:16:18.305966+00:00
-- url     : https://prove2.me/submissions/70dbca0b-b1d8-49b7-a28c-ab35758fc8fa

import Mathlib
import Definitions.Def_PolyhedralSOC_Sandwich_CQP

open PolyhedralSOC.Sandwich

theorem solution {n k₀ m : ℕ} (P : CQP n k₀ m) (ε : ℝ) (hε : 0 < ε) :
    feas P ⊆ feasRelaxed P ε := by
  intro x hx
  obtain ⟨hlin, hcone⟩ := hx
  refine ⟨hlin, fun l => ?_⟩
  have hle := hcone l
  refine hle.trans ?_
  have hnn : (0:ℝ) ≤ P.c l ⬝ᵥ x - P.d l := by
    refine le_trans ?_ hle
    simp only [eucNorm]
    exact Real.sqrt_nonneg _
  nlinarith
