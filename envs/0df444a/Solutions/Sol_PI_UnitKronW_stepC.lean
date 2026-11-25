-- Prove2me | solution 1 for PI.UnitKronW.stepC
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T10:43:22.323425+00:00
-- url     : https://prove2.me/submissions/8ac9b12a-d24b-49b4-908c-d9b86820bbfc

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitKronecker_PosDefFormNeZero
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitKronecker_EqZeroOfMulVec
import Theorems.Thm_PI_UnitKronW_pres_pow
import Theorems.Thm_PI_UnitKronW_unip_pow
import Theorems.Thm_PI_UnitKronW_charpoly_dvd

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PI PI.UnitKronW
open Matrix Polynomial ComplexOrder
namespace PI.UnitKronW
theorem _root_.solution : StepC := by
  unfold StepC
  intro k H G hH hG n hn
  have hW := pres_pow hG n
  have hdvd := charpoly_dvd G n hn
  have h0 : (G ^ n - 1) ^ k = 0 := by
    obtain ⟨q, hq⟩ := hdvd
    have h := congrArg (Polynomial.aeval G) hq
    rw [map_mul, Matrix.aeval_self_charpoly, zero_mul] at h
    simpa using h
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · ext i j
    exact Fin.elim0 i
  · have h1 := unip_pow hH hW (k - 1) (by rw [Nat.sub_add_cancel hk]; exact h0)
    exact sub_eq_zero.mp h1
end PI.UnitKronW
