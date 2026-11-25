-- Prove2me | solution 1 for PI.PolynomialProperness.CB.lt_entry_bound
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T10:46:54.736559+00:00
-- url     : https://prove2.me/submissions/63f4547c-57eb-428b-a65c-d8e355a24532

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PolynomialProperness_NsqMulVecLe
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PolynomialProperness_SecondOrderNormBound
import Theorems.Thm_PI_PolynomialProperness_CB_mx_transpose
import Theorems.Thm_PI_PolynomialProperness_CB_ut_entry_bound

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
theorem _root_.solution {m : ℕ} {L U : Matrix (Fin m) (Fin m) ℂ} (hL : L ∈ LTset m)
    (hU : U ∈ UTset m) (i j : Fin m) : ‖L i j‖ ≤ m.factorial * (1 + mx (L * U)) ^ m := by
  have hUt : Uᵀ ∈ LTset m :=
    ⟨fun a b hab => by rw [transpose_apply]; exact hU.1 _ _ hab, fun a => hU.2 a⟩
  have hLt : Lᵀ ∈ UTset m :=
    ⟨fun a b hab => by rw [transpose_apply]; exact hL.1 _ _ hab, fun a => hL.2 a⟩
  have h := ut_entry_bound hUt hLt j i
  rwa [← transpose_mul, mx_transpose, transpose_apply] at h
end PI.PolynomialProperness.CB
