-- Prove2me | solution 1 for PlotkinShmoysTardos.exact_solution_cost_nonpos
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-02T22:26:17.239471+00:00
-- url     : https://prove2.me/submissions/494ebc88-0a33-42fd-b9ef-8b127bd69346

import Mathlib
import Definitions.Def_PlotkinShmoysTardos_General

open Finset Matrix PlotkinShmoysTardos

theorem solution {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ)
    (P : Set (Fin n → ℝ)) (hex : ∃ z, IsExact A b P z) (y : Fin m → ℝ) (hy : 0 ≤ y)
    (x' : Fin n → ℝ) (hx' : x' ∈ P)
    (hmin : ∀ z ∈ P, y ⬝ᵥ (A.mulVec x' - b) ≤ y ⬝ᵥ (A.mulVec z - b)) :
    y ⬝ᵥ (A.mulVec x' - b) ≤ 0 := by
  let _ := hx'
  rcases hex with ⟨z, hzP, hz_le⟩
  have h1 : y ⬝ᵥ (A.mulVec x' - b) ≤ y ⬝ᵥ (A.mulVec z - b) := hmin z hzP
  have h2 : y ⬝ᵥ (A.mulVec z - b) ≤ 0 := by
    simp only [dotProduct, Pi.sub_apply]
    refine sum_nonpos fun i _ => ?_
    exact mul_nonpos_of_nonneg_of_nonpos (hy i) (sub_nonpos.mpr (hz_le i))
  exact h1.trans h2
