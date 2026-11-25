-- Prove2me | solution 1 for P2M_GroundTheory_Global_Matrix_det_blockDiagonal__9aefd9cf488d
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T02:33:40.873465+00:00
-- url     : https://prove2.me/submissions/62ed073b-604d-4dba-acaf-79e35b061ab2

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_SemilocalAlgebras_Infinite

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GroundTheory GroundTheory.Global
open NumberField NumberField.InfinitePlace NumberField.InfinitePlace.Completion
open scoped NumberField.LiesOver TensorProduct
open GroundTheory.Global.Matrix
namespace GroundTheory.Global.Matrix
theorem _root_.solution {R ι : Type*} [CommRing R] [Fintype ι] [DecidableEq ι] {κ : ι → Type*}
    [∀ i, Fintype (κ i)] [∀ i, DecidableEq (κ i)] (M : ∀ i, Matrix (κ i) (κ i) R) :
    (Matrix.blockDiagonal' M).det = ∏ i, (M i).det := by
  classical
  let _ : LinearOrder ι := LinearOrder.lift' (Fintype.equivFin ι) (Fintype.equivFin ι).injective
  rw [(Matrix.blockTriangular_blockDiagonal' M).det]
  have hblock : ∀ a, ((Matrix.blockDiagonal' M).toSquareBlock Sigma.fst a).det = (M a).det := by
    intro a
    let e : κ a ≃ {x : (i : ι) × κ i // x.1 = a} :=
      { toFun := fun x => ⟨⟨a, x⟩, rfl⟩
        invFun := fun x => x.2 ▸ x.1.2
        left_inv := fun x => rfl
        right_inv := by rintro ⟨⟨i, x⟩, rfl⟩; rfl }
    rw [← Matrix.det_submatrix_equiv_self e]
    congr 1
    ext x y
    simp [Matrix.toSquareBlock, Matrix.toSquareBlockProp, e, Matrix.blockDiagonal'_apply_eq]
  simp_rw [hblock]
  refine Finset.prod_subset (Finset.subset_univ _) fun a _ ha => ?_
  have : IsEmpty (κ a) := ⟨fun x => ha (Finset.mem_image.2 ⟨⟨a, x⟩, Finset.mem_univ _, rfl⟩)⟩
  exact Matrix.det_isEmpty
end GroundTheory.Global.Matrix
