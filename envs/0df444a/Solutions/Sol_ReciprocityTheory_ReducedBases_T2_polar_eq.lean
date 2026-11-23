-- Prove2me | solution 1 for ReciprocityTheory.ReducedBases.T2.polar_eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:24:31.414153+00:00
-- url     : https://prove2.me/submissions/662dcd98-147e-4d94-a32f-53085dc03426

import Definitions.Def_ReciprocityTheory_ReducedBases_GsInnerBOfLt
import Definitions.Def_ReciprocityTheory_ReducedBases_LatDefs
import Definitions.Def_ReciprocityTheory_ReducedBases_TBInjective
import Theorems.Thm_ReciprocityTheory_ReducedBases_T2_fB_apply

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ReducedBases ReciprocityTheory.ReducedBases.T2
open Finset InnerProductSpace Matrix
variable {d : ℕ}
namespace ReciprocityTheory.ReducedBases.T2
theorem _root_.solution (A B : Matrix (Fin d) (Fin d) ℝ) (hAB : A = Bᴴ * B) (x y : Fin d → ℤ) :
    polar A x y = ⟪fB B x, fB B y⟫_ℝ := by
  subst hAB
  rw [fB_apply, fB_apply, polar, Matrix.conjTranspose_eq_transpose_of_trivial,
    ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, Matrix.vecMul_transpose]
  simp [PiLp.inner_apply, dotProduct, mul_comm]
end ReciprocityTheory.ReducedBases.T2
