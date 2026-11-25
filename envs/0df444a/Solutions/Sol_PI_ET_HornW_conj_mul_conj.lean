-- Prove2me | solution 1 for PI.ET.HornW.conj_mul_conj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T09:38:09.616062+00:00
-- url     : https://prove2.me/submissions/1cd8a0f5-b341-4e35-87bb-378b41a90fb1

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_ExpTri
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ExponentialTriangular_SortedSpec
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ExponentialTriangular_NormDetConjExp
import Theorems.Thm_PI_ET_HornW_unit_star_mul

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
theorem _root_.solution {W : Matrix (Fin n) (Fin n) ℂ} (hW : W ∈ unitaryGroup (Fin n) ℂ)
    (d e : Fin n → ℂ) :
    (W * diagonal d * Wᴴ) * (W * diagonal e * Wᴴ) = W * diagonal (fun i => d i * e i) * Wᴴ := by
  calc (W * diagonal d * Wᴴ) * (W * diagonal e * Wᴴ)
      = W * (diagonal d * (Wᴴ * W) * diagonal e) * Wᴴ := by simp only [Matrix.mul_assoc]
    _ = W * diagonal (fun i => d i * e i) * Wᴴ := by
      rw [unit_star_mul hW, Matrix.mul_one, diagonal_mul_diagonal]
end PI.ET.HornW
