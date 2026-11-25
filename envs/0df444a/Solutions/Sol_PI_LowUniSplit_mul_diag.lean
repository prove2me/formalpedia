-- Prove2me | solution 1 for PI.LowUniSplit.mul_diag
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T10:09:49.946824+00:00
-- url     : https://prove2.me/submissions/5eaca13e-fa0c-49ad-8635-a6223c0cad73

import Definitions.Def_Formalism_HermitianCurvature_FiniteOrderIntersectionInSmooth
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LowerUnipotentSplit_SecondFactorMemLowerTriangular

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
open PI PI.LowUniSplit
open Formalism.FourierDecayAlt.C2
variable {m : ℕ}
namespace PI.LowUniSplit
theorem _root_.solution {a b : Matrix (Fin m) (Fin m) ℂ} (ha : a ∈ LTset m) (hb : b ∈ LTset m)
    (i : Fin m) : (a * b) i i = 1 := by
  rw [Matrix.mul_apply, Finset.sum_eq_single i]
  · rw [ha.2, hb.2, one_mul]
  · intro k _ hk
    rcases lt_or_gt_of_ne hk with h | h
    · rw [hb.1 k i h, mul_zero]
    · rw [ha.1 i k h, zero_mul]
  · simp
end PI.LowUniSplit
