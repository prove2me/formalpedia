-- Prove2me | solution 1 for PI.PolynomialProperness.CB.mx_transpose
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T10:04:26.692549+00:00
-- url     : https://prove2.me/submissions/ca3bb92d-6a29-4684-be9d-373f68618e5a

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PolynomialProperness_NsqMulVecLe
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PolynomialProperness_SecondOrderNormBound
import Theorems.Thm_PI_PolynomialProperness_GN_entry_le_mx
import Theorems.Thm_PI_PolynomialProperness_GN_mx_le_iff
import Theorems.Thm_PI_PolynomialProperness_GN_mx_nonneg


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Formalism.FourierDecayAlt.C2
noncomputable section
open PI PI.PolynomialProperness PI.PolynomialProperness.CB
namespace PI.PolynomialProperness.CB
theorem _root_.solution {m : ℕ} (M : Matrix (Fin m) (Fin m) ℂ) : mx Mᵀ = mx M := by
  apply le_antisymm
  · refine (GN.mx_le_iff _ (GN.mx_nonneg M)).2 fun i j => ?_
    rw [transpose_apply]; exact GN.entry_le_mx M j i
  · refine (GN.mx_le_iff _ (GN.mx_nonneg Mᵀ)).2 fun i j => ?_
    have := GN.entry_le_mx Mᵀ j i
    rwa [transpose_apply] at this
end PI.PolynomialProperness.CB
