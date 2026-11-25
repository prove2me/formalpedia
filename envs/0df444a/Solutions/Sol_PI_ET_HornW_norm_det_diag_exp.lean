-- Prove2me | solution 1 for PI.ET.HornW.norm_det_diag_exp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T09:37:32.461593+00:00
-- url     : https://prove2.me/submissions/26f619f3-5e17-425c-a43a-b5cb73a4742f

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_ExpTri
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ExponentialTriangular_SortedSpec
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ExponentialTriangular_NormDetConjExp
import Theorems.Thm_PI_ET_HornW_psum_eq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset
open scoped MatrixOrder ComplexOrder
noncomputable section
open PI PI.ET
open PI.ET.HornW
variable {n : ℕ}
namespace PI.ET.HornW
theorem _root_.solution {k : ℕ} (hk : k ≤ n) (f : Fin n → ℝ) :
    ‖(diagonal (fun i : Fin k => (Real.exp (2 * f (Fin.castLE hk i)) : ℂ))).det‖ =
      Real.exp (2 * psum f k) := by
  rw [Matrix.det_diagonal, norm_prod]
  simp only [Complex.norm_real, Real.norm_eq_abs, Real.abs_exp]
  rw [psum_eq hk, Finset.mul_sum, Real.exp_sum]
end PI.ET.HornW
