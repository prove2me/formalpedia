-- Prove2me | solution 1 for PI.ET.HornW.conj_herm
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:27:16.486632+00:00
-- url     : https://prove2.me/submissions/66df6bf0-ba48-4b5b-83d4-62e05ede9366

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_ExpTri
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ExponentialTriangular_SortedSpec
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ExponentialTriangular_NormDetConjExp

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
theorem _root_.solution (W : Matrix (Fin n) (Fin n) ℂ) (r : Fin n → ℝ) :
    (W * diagonal (fun i => (r i : ℂ)) * Wᴴ)ᴴ = W * diagonal (fun i => (r i : ℂ)) * Wᴴ := by
  rw [conjTranspose_mul, conjTranspose_mul, conjTranspose_conjTranspose, diagonal_conjTranspose,
    Matrix.mul_assoc]
  congr 3
  funext i
  simp
end PI.ET.HornW
