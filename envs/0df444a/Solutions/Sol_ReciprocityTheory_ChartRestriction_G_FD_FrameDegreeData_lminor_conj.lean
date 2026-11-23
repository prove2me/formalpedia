-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.FD.FrameDegreeData.lminor_conj
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T16:53:37.638514+00:00
-- url     : https://prove2.me/submissions/420c7abf-3951-41e6-9892-7c4064313f5f

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_IsotropicCoefficientSplitting
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_DetSubUpper
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_FrameDegreeData_sub_mul_sub
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_FrameDegreeData_upper_lt
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_FrameDegreeData_det_sub_upper

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FD.FrameDegreeData
open NumberField Complex Matrix
open scoped ComplexConjugate
noncomputable section
variable {n : ℕ}
namespace ReciprocityTheory.ChartRestriction.G.FD.FrameDegreeData
theorem _root_.solution {N A : Matrix (Fin n) (Fin n) ℂ} (hN : N.BlockTriangular id) (i : Fin (n + 1)) :
    lminor (Nᵀ * A * N.map (starRingEnd ℂ)) i =
      (∏ j : Fin i, N (Fin.castLE (Nat.le_of_lt_succ i.isLt) j) (Fin.castLE (Nat.le_of_lt_succ i.isLt) j)) *
        lminor A i *
        conj (∏ j : Fin i, N (Fin.castLE (Nat.le_of_lt_succ i.isLt) j) (Fin.castLE (Nat.le_of_lt_succ i.isLt) j)) := by
  have h := Nat.le_of_lt_succ i.isLt
  unfold lminor
  rw [sub_mul_sub h (Nᵀ * A) (N.map (starRingEnd ℂ)) (fun a c k hk => ?_),
    sub_mul_sub h Nᵀ A (fun a c k hk => ?_), Matrix.det_mul, Matrix.det_mul, ← Matrix.transpose_submatrix, Matrix.det_transpose,
    det_sub_upper h hN]
  · congr 1
    rw [show (N.map (starRingEnd ℂ)).submatrix (Fin.castLE h) (Fin.castLE h) =
        (starRingEnd ℂ).mapMatrix (N.submatrix (Fin.castLE h) (Fin.castLE h)) from rfl,
      ← RingHom.map_det, det_sub_upper h hN]
  all_goals
    have h1 : N k (Fin.castLE h c) = 0 :=
      upper_lt hN (show Fin.castLE h c < k by rw [Fin.lt_def]; simp; omega)
    have h2 : N k (Fin.castLE h a) = 0 :=
      upper_lt hN (show Fin.castLE h a < k by rw [Fin.lt_def]; simp; omega)
    simp [h1, h2]
end ReciprocityTheory.ChartRestriction.G.FD.FrameDegreeData
