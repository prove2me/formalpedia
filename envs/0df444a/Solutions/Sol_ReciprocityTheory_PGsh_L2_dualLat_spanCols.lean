-- Prove2me | solution 1 for ReciprocityTheory.PGsh.L2.dualLat_spanCols
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T15:43:07.764164+00:00
-- url     : https://prove2.me/submissions/d409b8b6-5157-4c08-95f5-c9bfa3e1ad8e

import Definitions.Def_ReciprocityTheory_DualLattices_TensorSpan
import Definitions.Def_ReciprocityTheory_DualLattices_ValuationDetEqOfSpanEq
import Theorems.Thm_ReciprocityTheory_PGsh_L2_mem_spanCols_iff_inv
import Theorems.Thm_ReciprocityTheory_PGsh_L2_mem_dualLat_spanCols_iff

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
theorem _root_.solution (B : Matrix X X C) (hB : IsUnit B.det) :
    dualLat (Submodule.span R (Set.range fun j x => B x j)) =
      Submodule.span R (Set.range fun j x => (B⁻¹)ᵀ x j) := by
  have hBT : IsUnit (B⁻¹)ᵀ.det := by
    rw [Matrix.det_transpose]
    exact Matrix.isUnit_nonsing_inv_det _ hB
  ext u
  rw [mem_dualLat_spanCols_iff, mem_spanCols_iff_inv _ hBT, ← Matrix.transpose_nonsing_inv,
    Matrix.nonsing_inv_nonsing_inv _ hB, Matrix.mulVec_transpose]
end ReciprocityTheory.PGsh.L2
