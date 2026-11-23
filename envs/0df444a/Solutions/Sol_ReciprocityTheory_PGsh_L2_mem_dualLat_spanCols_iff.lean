-- Prove2me | solution 1 for ReciprocityTheory.PGsh.L2.mem_dualLat_spanCols_iff
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:22:49.158343+00:00
-- url     : https://prove2.me/submissions/861ebbab-71c0-4242-b69d-2eb0b6ea9979

import Definitions.Def_ReciprocityTheory_DualLattices_TensorSpan
import Definitions.Def_ReciprocityTheory_DualLattices_ValuationDetEqOfSpanEq
import Theorems.Thm_ReciprocityTheory_PGsh_L2_mem_spanCols_iff

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset Matrix
open ReciprocityTheory ReciprocityTheory.PGsh ReciprocityTheory.PGsh.L2
variable {C : Type} [Field C] {R : Type} [CommRing R] [Algebra R C]
variable {X : Type} [Fintype X] [DecidableEq X]
namespace ReciprocityTheory.PGsh.L2
theorem _root_.solution (B : Matrix X X C) (u : X → C) :
    u ∈ dualLat (Submodule.span R (Set.range fun j x => B x j)) ↔ u ᵥ* B ∈ intFun (C := C) R X := by
  constructor
  · intro h j
    obtain ⟨r, hr⟩ := h _ (Submodule.subset_span ⟨j, rfl⟩)
    exact ⟨r, by rw [hr]; simp [Matrix.vecMul, dotProduct]⟩
  · intro h f hf
    obtain ⟨w, hw, rfl⟩ := (mem_spanCols_iff B f).1 hf
    choose r hr using h
    choose s hs using hw
    refine ⟨∑ j, r j * s j, ?_⟩
    simp only [map_sum, map_mul, hr, hs, Matrix.vecMul, dotProduct, Matrix.mulVec,
      Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun j _ => ?_
    ring
end ReciprocityTheory.PGsh.L2
