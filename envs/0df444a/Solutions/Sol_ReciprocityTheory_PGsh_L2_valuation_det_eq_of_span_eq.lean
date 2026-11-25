-- Prove2me | solution 1 for ReciprocityTheory.PGsh.L2.valuation_det_eq_of_span_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T15:46:10.835122+00:00
-- url     : https://prove2.me/submissions/b9d3fdec-fb9c-4a99-822d-efa1e0319fd0

import Definitions.Def_ReciprocityTheory_DualLattices_TensorSpan
import Definitions.Def_ReciprocityTheory_DualLattices_ValuationDetEqOfSpanEq
import Theorems.Thm_ReciprocityTheory_PGsh_L2_mem_spanCols_iff
import Theorems.Thm_ReciprocityTheory_PGsh_L2_valuation_det_le_one

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
theorem _root_.solution (v : Valuation C NNReal) (hv : v.Integers R)
    (B B' : Matrix X X C)
    (h : Submodule.span R (Set.range fun j x => B x j) =
      Submodule.span R (Set.range fun j x => B' x j)) : v B.det = v B'.det := by
  have key : ∀ (B B' : Matrix X X C),
      Submodule.span R (Set.range fun j x => B x j) ≤
        Submodule.span R (Set.range fun j x => B' x j) → v B.det ≤ v B'.det := by
    intro B B' hle
    have hcol : ∀ j, ∃ w ∈ intFun (C := C) R X, (fun x => B x j) = B' *ᵥ w := fun j =>
      (mem_spanCols_iff B' _).1 (hle (Submodule.subset_span ⟨j, rfl⟩))
    choose w hw hBw using hcol
    have hBP : B = B' * Matrix.of fun x j => w j x := by
      ext x j
      have := congrFun (hBw j) x
      simpa [Matrix.mul_apply, Matrix.mulVec, dotProduct] using this
    have hle1 : v (Matrix.of fun x j => w j x).det ≤ 1 :=
      valuation_det_le_one v hv _ fun x j => hw j x
    rw [hBP, Matrix.det_mul, map_mul]
    exact mul_le_of_le_one_right' hle1
  exact le_antisymm (key B B' h.le) (key B' B h.ge)
end ReciprocityTheory.PGsh.L2
