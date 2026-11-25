-- Prove2me | solution 1 for PI.ET.HornW.sq_conj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T09:42:58.984216+00:00
-- url     : https://prove2.me/submissions/0f8c7def-11cb-41c1-9bef-59b81f6ec876

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_ExpTri
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ExponentialTriangular_SortedSpec
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ExponentialTriangular_NormDetConjExp
import Theorems.Thm_PI_ET_HornW_conj_mul_conj

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
    (W * diagonal (fun i => (Real.exp (d i) : ℂ)) * Wᴴ) *
        (W * diagonal (fun i => (Real.exp (d i) : ℂ)) * Wᴴ) =
      W * diagonal (fun i => (Real.exp (2 * d i) : ℂ)) * Wᴴ := by
  rw [conj_mul_conj hW]
  congr 3
  funext i
  simp only [two_mul, Real.exp_add, Complex.ofReal_mul]
end PI.ET.HornW
