-- Prove2me | solution 1 for PI.ET.HornW.prod_exp_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T09:37:40.390811+00:00
-- url     : https://prove2.me/submissions/6b000b90-d9c6-4def-9a69-95962519e6d6

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
    ∏ i : Fin k, Real.exp (2 * f (Fin.castLE hk i)) = Real.exp (2 * psum f k) := by
  rw [psum_eq hk, Finset.mul_sum, Real.exp_sum]
end PI.ET.HornW
