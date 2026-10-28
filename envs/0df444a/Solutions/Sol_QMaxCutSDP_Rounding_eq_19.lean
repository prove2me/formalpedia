-- Prove2me | solution 1 for QMaxCutSDP.Rounding.eq_19
-- status  : ACCEPTED   (prove)
-- author  : @Ethan Cheung Wang
-- created : 2026-10-21T20:52:07.921837+00:00
-- url     : https://prove2.me/submissions/130c4c4d-e787-4d41-a8d6-757cfe7b841e

import Mathlib
import Definitions.Def_QMaxCutSDP_Rounding_Model

open Matrix MeasureTheory
open QMaxCutSDP.Rounding

theorem solution {n N : ℕ} (v : SDPVec n N) (hv : IsSFeasible v)
    (i j : Fin n) (hij : i ≠ j) :
    gammaE v i j = -(1 + vEdge v i j ⬝ᵥ v.v0) / 2 ∧
    (v.v0 - vEdge v i j) ⬝ᵥ v.v0 = 2 * (1 + gammaE v i j) := by
  obtain ⟨h0, -, -, hn, -, -, -, hab, -⟩ := hv
  have n0 := hn i j 0 hij
  have n1 := hn i j 1 hij
  have n2 := hn i j 2 hij
  have p01 := hab i j 0 1 2 hij (by decide) (by decide) (by decide)
  have p10 := hab i j 1 0 2 hij (by decide) (by decide) (by decide)
  have p02 := hab i j 0 2 1 hij (by decide) (by decide) (by decide)
  have p20 := hab i j 2 0 1 hij (by decide) (by decide) (by decide)
  have p12 := hab i j 1 2 0 hij (by decide) (by decide) (by decide)
  have p21 := hab i j 2 1 0 hij (by decide) (by decide) (by decide)
  have c0 := dotProduct_comm v.v0 (v.vij i j 0)
  have c1 := dotProduct_comm v.v0 (v.vij i j 1)
  have c2 := dotProduct_comm v.v0 (v.vij i j 2)
  have hE : vEdge v i j = v.vij i j 0 + v.vij i j 1 + v.vij i j 2 := by
    simp [vEdge, Fin.sum_univ_three]
  have hw : (v.v0 + vEdge v i j) ⬝ᵥ (v.v0 + vEdge v i j) = 4 := by
    rw [hE]
    simp only [add_dotProduct, dotProduct_add]
    linear_combination h0 + n0 + n1 + n2 + p01 + p10 + p02 + p20 + p12 + p21 + c0 + c1 + c2
  have hg : gammaE v i j = -(1 + vEdge v i j ⬝ᵥ v.v0) / 2 := by
    unfold gammaE
    rw [hw, h0, add_dotProduct, h0]
    have : Real.sqrt 4 = 2 := by
      rw [show (4:ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
    rw [this, Real.sqrt_one]
    ring
  refine ⟨hg, ?_⟩
  rw [hg, sub_dotProduct, h0]
  ring
