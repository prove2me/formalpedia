-- Prove2me | solution 1 for ReciprocityTheory.PGsh.L2.mem_spanCols_iff_inv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T15:28:01.82528+00:00
-- url     : https://prove2.me/submissions/461b95e4-6394-48cc-a660-7320775a07c4

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
theorem _root_.solution (B : Matrix X X C) (hB : IsUnit B.det) (f : X → C) :
    f ∈ Submodule.span R (Set.range fun j x => B x j) ↔ B⁻¹ *ᵥ f ∈ intFun (C := C) R X := by
  rw [mem_spanCols_iff]
  constructor
  · rintro ⟨w, hw, rfl⟩
    rwa [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hB, Matrix.one_mulVec]
  · intro h
    exact ⟨_, h, by rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hB, Matrix.one_mulVec]⟩
end ReciprocityTheory.PGsh.L2
