-- Prove2me | solution 1 for PI.StabBigW.g_mul_out
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T10:31:49.250281+00:00
-- url     : https://prove2.me/submissions/7c7187d9-5d1e-426f-9504-58ca622d5f5e

import Definitions.Def_Formalism_PeriodIntegrals_StabBig
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_UnitaryWeylNormalHolds
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LargeStabilizerInverse_GLeftInv
import Theorems.Thm_PI_StabBigW_g_row_out

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
noncomputable section
open PI PI.StabBigW
open Formalism.QuantumDeterminants Formalism.QuantumDeterminants.WeylGroupFacts
variable {k r : ℕ}
namespace PI.StabBigW
theorem _root_.solution (c : Fin r → ℂ) (μ : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ)
    (B : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ)
    (i j : Fin (2 * r + k + 1)) (hi : i.val < r ∨ r + k < i.val) :
    (bigCell k r c μ * B) i j = dd k r c (tau k r i) * B (tau k r i) j := by
  have hrow : ∀ m, bigCell k r c μ i m = if m = tau k r i then dd k r c (tau k r i) else 0 :=
    fun m => g_row_out c μ i m hi
  rw [Matrix.mul_apply]
  simp only [hrow, ite_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
end PI.StabBigW
