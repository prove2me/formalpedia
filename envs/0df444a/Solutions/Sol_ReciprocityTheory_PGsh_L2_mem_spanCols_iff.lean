-- Prove2me | solution 1 for ReciprocityTheory.PGsh.L2.mem_spanCols_iff
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:17:57.628931+00:00
-- url     : https://prove2.me/submissions/2fb16e56-0fc5-401e-b340-730df9eef5ae

import Definitions.Def_ReciprocityTheory_DualLattices_TensorSpan
import Definitions.Def_ReciprocityTheory_DualLattices_ValuationDetEqOfSpanEq

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
theorem _root_.solution (B : Matrix X X C) (f : X → C) :
    f ∈ Submodule.span R (Set.range fun j x => B x j) ↔ ∃ w ∈ intFun (C := C) R X, f = B *ᵥ w := by
  rw [Submodule.mem_span_range_iff_exists_fun]
  constructor
  · rintro ⟨c, rfl⟩
    refine ⟨fun j => algebraMap R C (c j), fun j => ⟨c j, rfl⟩, ?_⟩
    ext x
    simp [Matrix.mulVec, dotProduct, Finset.sum_apply, Algebra.smul_def, mul_comm]
  · rintro ⟨w, hw, rfl⟩
    choose c hc using hw
    refine ⟨c, ?_⟩
    ext x
    simp [Matrix.mulVec, dotProduct, Finset.sum_apply, Algebra.smul_def, hc, mul_comm]
end ReciprocityTheory.PGsh.L2
