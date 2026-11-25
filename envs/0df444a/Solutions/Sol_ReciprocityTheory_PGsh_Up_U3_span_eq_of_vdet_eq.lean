-- Prove2me | solution 1 for ReciprocityTheory.PGsh.Up.U3.span_eq_of_vdet_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T15:47:28.614809+00:00
-- url     : https://prove2.me/submissions/6ecdc489-9f3d-47d3-ba0b-c54650bdb98b

import Definitions.Def_ReciprocityTheory_DualLattices_ValuationDetEqOfSpanEq
import Definitions.Def_ReciprocityTheory_DualLattices_IsUnitDetOfSpanEq
import Definitions.Def_ReciprocityTheory_DualLattices_VIntCastLtOneOfDvd
import Definitions.Def_ReciprocityTheory_DualLattices_VdetLeOfSpanLe
import Theorems.Thm_ReciprocityTheory_PGsh_L2_det_map_algebraMap
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
open ReciprocityTheory ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.Up.U3
open ReciprocityTheory.PGsh.L2
variable {C : Type} [Field C] {R : Type} [CommRing R] [Algebra R C] {v : Valuation C NNReal}
variable {X : Type} [Fintype X] [DecidableEq X]
namespace ReciprocityTheory.PGsh.Up.U3
theorem _root_.solution (hv : v.Integers R) {B B' : Matrix X X C} (hB' : IsUnit B'.det)
    (hle : Submodule.span R (Set.range fun j x => B x j) ≤
      Submodule.span R (Set.range fun j x => B' x j)) (hdet : v B.det = v B'.det) :
    Submodule.span R (Set.range fun j x => B x j) =
      Submodule.span R (Set.range fun j x => B' x j) := by
  refine le_antisymm hle ?_
  have hcol : ∀ j, ∃ w ∈ intFun (C := C) R X, (fun x => B x j) = B' *ᵥ w := fun j =>
    (mem_spanCols_iff B' _).1 (hle (Submodule.subset_span ⟨j, rfl⟩))
  choose w hw hBw using hcol
  choose r hr using hw
  set W0 : Matrix X X R := Matrix.of fun x j => r j x with hW0
  have hBW : B = B' * W0.map (algebraMap R C) := by
    ext x j
    rw [show B x j = (B' *ᵥ w j) x from congrFun (hBw j) x]
    simp [Matrix.mul_apply, Matrix.mulVec, dotProduct, W0, hr]
  have hne : v B'.det ≠ 0 := (Valuation.ne_zero_iff v).2 hB'.ne_zero
  have hW1 : v (algebraMap R C W0.det) = 1 := by
    have h := hdet
    rw [hBW, Matrix.det_mul, map_mul, det_map_algebraMap] at h
    exact mul_left_cancel₀ hne (h.trans (mul_one _).symm)
  have hU : IsUnit W0.det := hv.isUnit_of_one' hW1
  have hB'eq : B' = B * (W0⁻¹).map (algebraMap R C) := by
    rw [hBW, Matrix.mul_assoc, ← Matrix.map_mul, Matrix.mul_nonsing_inv W0 hU,
      Matrix.map_one _ (map_zero _) (map_one _), Matrix.mul_one]
  rw [Submodule.span_le]
  rintro _ ⟨j, rfl⟩
  rw [SetLike.mem_coe, mem_spanCols_iff]
  refine ⟨fun k => algebraMap R C (W0⁻¹ k j), fun k => ⟨_, rfl⟩, ?_⟩
  ext x
  conv_lhs => rw [hB'eq]
  simp [Matrix.mul_apply, Matrix.mulVec, dotProduct]
end ReciprocityTheory.PGsh.Up.U3
