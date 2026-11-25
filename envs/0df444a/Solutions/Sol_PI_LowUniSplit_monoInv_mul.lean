-- Prove2me | solution 1 for PI.LowUniSplit.monoInv_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T10:14:49.513094+00:00
-- url     : https://prove2.me/submissions/327cf6de-5974-4075-be09-665a1b3dee9f

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
theorem _root_.solution (w : Equiv.Perm (Fin m)) (d : Fin m → ℂ) (hd : ∀ a, d a ≠ 0) :
    monoInv w d * monoP w d = 1 := by
  ext a b
  simp only [Matrix.mul_apply, monoInv, monoP, Matrix.of_apply, ite_mul, zero_mul,
    Finset.sum_ite_eq', Finset.mem_univ, if_true, Matrix.one_apply]
  by_cases h : a = b
  · subst h; simp [hd a]
  · have : w a ≠ w b := fun e => h (w.injective e)
    simp [this, h]
end PI.LowUniSplit
