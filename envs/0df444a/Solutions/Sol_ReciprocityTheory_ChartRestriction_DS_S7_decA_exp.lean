-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.S7.decA_exp
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:06:59.320427+00:00
-- url     : https://prove2.me/submissions/a2d94bb0-dae0-44db-9524-6dc63a0f3ea6

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_IsClosedKset
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_DecPos
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_DecLog
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_DecMoments
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_DecSum
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_ToMKMulInv
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_DecALogLower

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset MeasureTheory Matrix
open scoped ComplexOrder ContDiff ENNReal
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.S7
open ReciprocityTheory.ChartRestriction.DS
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {n : ℕ} {ε : Fin n → Bool}
namespace ReciprocityTheory.ChartRestriction.DS.S7
theorem _root_.solution {U : Matrix (Fin n) (Fin n) ℂ} (hU : U ∈ Matrix.unitaryGroup (Fin n) ℂ) (y : Fin n → ℝ) :
    NormedSpace.exp (U * Matrix.diagonal (fun j => (y j : ℂ)) * Uᴴ) =
      U * Matrix.diagonal (fun j => ((Real.exp (y j) : ℝ) : ℂ)) * Uᴴ := by
  have hinv : U⁻¹ = Uᴴ := by
    rw [← Matrix.star_eq_conjTranspose]
    exact Matrix.inv_eq_left_inv (Matrix.mem_unitaryGroup_iff'.mp hU)
  have hu : IsUnit U := (Matrix.isUnit_iff_isUnit_det U).mpr (isUnit_iff_ne_zero.mpr
    (left_ne_zero_of_mul_eq_one (b := (star U).det)
      (by rw [← Matrix.det_mul, Matrix.mem_unitaryGroup_iff.mp hU, Matrix.det_one])))
  have hd : NormedSpace.exp (fun j => ((y j : ℝ) : ℂ)) = fun j => ((Real.exp (y j) : ℝ) : ℂ) := by
    funext j
    first
      | (rw [Pi.exp_apply]; simp [← Complex.exp_eq_exp_ℂ, Complex.ofReal_exp])
      | (simp [Pi.exp_def, ← Complex.exp_eq_exp_ℂ, Complex.ofReal_exp])
      | (simp [NormedSpace.exp_pi, ← Complex.exp_eq_exp_ℂ, Complex.ofReal_exp])
  rw [← hinv, Matrix.exp_conj U _ hu, Matrix.exp_diagonal, hd]
end ReciprocityTheory.ChartRestriction.DS.S7
