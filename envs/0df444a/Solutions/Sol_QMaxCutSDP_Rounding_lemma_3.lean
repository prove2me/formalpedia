-- Prove2me | solution 1 for QMaxCutSDP.Rounding.lemma_3
-- status  : ACCEPTED   (prove)
-- author  : @Ethan Cheung
-- created : 2026-10-21T21:00:51.586624+00:00
-- url     : https://prove2.me/submissions/f8260f27-173d-43d1-907f-2fb027d6d4e6

import Mathlib
import Definitions.Def_QMaxCutSDP_Rounding_Model

open Matrix MeasureTheory
open QMaxCutSDP.Rounding

theorem solution {n N : ℕ} (v : SDPVec n N) (hv : IsSFeasible v) :
    (∀ i j : Fin n, i ≠ j →
      (vEdge v i j ⬝ᵥ vEdge v i j = 3 - 2 * (vEdge v i j ⬝ᵥ v.v0)) ∧
      ((v.v0 + vEdge v i j) ⬝ᵥ (v.v0 + vEdge v i j) = 4)) ∧
    (∀ i j k : Fin n, i ≠ j → j ≠ k → i ≠ k →
      vEdge v i j ⬝ᵥ vEdge v j k = vEdge v i k ⬝ᵥ v.v0) := by
  obtain ⟨h0, -, -, hn, -, htri, hoff, hab, -⟩ := hv
  have hE : ∀ i j, vEdge v i j = v.vij i j 0 + v.vij i j 1 + v.vij i j 2 := by
    intro i j; simp [vEdge, Fin.sum_univ_three]
  refine ⟨fun i j hij => ?_, fun i j k hij hjk hik => ?_⟩
  · have n0 := hn i j 0 hij
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
    have h1 : vEdge v i j ⬝ᵥ vEdge v i j = 3 - 2 * (vEdge v i j ⬝ᵥ v.v0) := by
      rw [hE]
      simp only [add_dotProduct, dotProduct_add]
      linear_combination n0 + n1 + n2 + p01 + p10 + p02 + p20 + p12 + p21
    refine ⟨h1, ?_⟩
    simp only [add_dotProduct, dotProduct_add, h1, h0, dotProduct_comm v.v0 (vEdge v i j)]
    ring
  · rw [hE i j, hE j k, hE i k]
    simp only [add_dotProduct, dotProduct_add]
    have d0 := htri i j k 0 hij hjk hik
    have d1 := htri i j k 1 hij hjk hik
    have d2 := htri i j k 2 hij hjk hik
    have o01 := hoff i j k 0 1 hij hjk hik (by decide)
    have o02 := hoff i j k 0 2 hij hjk hik (by decide)
    have o10 := hoff i j k 1 0 hij hjk hik (by decide)
    have o12 := hoff i j k 1 2 hij hjk hik (by decide)
    have o20 := hoff i j k 2 0 hij hjk hik (by decide)
    have o21 := hoff i j k 2 1 hij hjk hik (by decide)
    linear_combination d0 + d1 + d2 + o01 + o02 + o10 + o12 + o20 + o21
