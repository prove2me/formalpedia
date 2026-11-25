-- Prove2me | solution 1 for PI.StabBigW.vec_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T10:31:36.320786+00:00
-- url     : https://prove2.me/submissions/2820d444-f36c-475a-9d85-c38fbccbb9bb

import Definitions.Def_Formalism_PeriodIntegrals_StabBig
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_UnitaryWeylNormalHolds
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LargeStabilizerInverse_GLeftInv

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
theorem _root_.solution {μ L : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ} (h : μ * L = 1)
    (v : Fin (k + 1) → ℂ) (hv : ∀ t, ∑ s, v s * μ s t = 0) : v = 0 := by
  have h1 : Matrix.vecMul v μ = 0 := by
    funext t
    rw [Pi.zero_apply, ← hv t]
    rfl
  calc v = Matrix.vecMul v (μ * L) := by rw [h, Matrix.vecMul_one]
    _ = Matrix.vecMul (Matrix.vecMul v μ) L := by rw [Matrix.vecMul_vecMul]
    _ = 0 := by rw [h1, Matrix.zero_vecMul]
end PI.StabBigW
