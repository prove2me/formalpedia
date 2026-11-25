-- Prove2me | solution 1 for ReciprocityTheory.PGsh.Up.DeterminantValuationBounds.v_det_le_of_cols
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T16:10:55.054303+00:00
-- url     : https://prove2.me/submissions/83ff8951-b5f9-42be-ab0a-27d3ed6e42bc

import Definitions.Def_ReciprocityTheory_DualLattices_ColengthSqBlockVandermonde
import Definitions.Def_ReciprocityTheory_DualLattices_ValuationPairwiseDifferenceProductPowLeColengthS
import Theorems.Thm_ReciprocityTheory_PGsh_IsIntegralMat_det_le_one
import Theorems.Thm_ReciprocityTheory_PGsh_IsIntegralMat_mulVec


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix
open ReciprocityTheory ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up
open ReciprocityTheory.PGsh.L2
open ReciprocityTheory.PGsh.Up.DeterminantValuationBounds
variable {C : Type} [Field C] {v : Valuation C NNReal}
variable {n s : ℕ}
namespace ReciprocityTheory.PGsh.Up.DeterminantValuationBounds
theorem _root_.solution {ι : Type} [Fintype ι] [DecidableEq ι] (L : Lat v ι) (X : Matrix ι ι C)
    (hX : ∀ y, (fun x => X x y) ∈ L.pts) : v X.det ≤ v L.B.det := by
  choose c hc using hX
  set U : Matrix ι ι C := Matrix.of fun i y => c y i with hU
  have hXe : X = L.B * U := by
    ext x y
    rw [show X x y = (L.B *ᵥ c y) x from congrFun (hc y).2 x, Matrix.mul_apply, Matrix.mulVec,
      dotProduct]
    simp [hU]
  have hUi : IsIntegralMat v U := fun i y => by simpa [hU] using (hc y).1 i
  rw [hXe, Matrix.det_mul, map_mul]
  exact mul_le_of_le_one_right zero_le hUi.det_le_one
end ReciprocityTheory.PGsh.Up.DeterminantValuationBounds
