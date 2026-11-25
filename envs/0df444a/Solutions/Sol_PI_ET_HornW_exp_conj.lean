-- Prove2me | solution 1 for PI.ET.HornW.exp_conj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T09:37:03.221125+00:00
-- url     : https://prove2.me/submissions/943dd622-3324-4311-8945-97cc3673950d

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_ExpTri
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ExponentialTriangular_SortedSpec
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ExponentialTriangular_NormDetConjExp
import Theorems.Thm_PI_ET_HornW_unit_star_mul
import Theorems.Thm_PI_ET_HornW_unit_mul_star

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
theorem _root_.solution {W : Matrix (Fin n) (Fin n) ℂ} (hW : W ∈ unitaryGroup (Fin n) ℂ) (d : Fin n → ℝ) :
    NormedSpace.exp (W * diagonal (fun i => (d i : ℂ)) * Wᴴ) =
      W * diagonal (fun i => (Real.exp (d i) : ℂ)) * Wᴴ := by
  have hinv : W⁻¹ = Wᴴ := Matrix.inv_eq_left_inv (unit_star_mul hW)
  have hu : IsUnit W :=
    (Matrix.isUnit_iff_isUnit_det W).mpr (Matrix.isUnit_det_of_right_inverse (unit_mul_star hW))
  rw [← hinv, Matrix.exp_conj W _ hu, Matrix.exp_diagonal, Pi.exp_def]
  congr 3
  funext i
  rw [Complex.ofReal_exp, Complex.exp_eq_exp_ℂ]
end PI.ET.HornW
