-- Prove2me | solution 1 for PI.WGL.XiU.normSq_sum_mulVec
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T11:20:38.411594+00:00
-- url     : https://prove2.me/submissions/1f6b9c3e-ad44-49c9-bbb3-5620b3ad7983

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinLowering_MultisetProdNormLeOne
import Theorems.Thm_PI_WGL_XiU_normSq_sum_eq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.WGL PI.WGL.XiU
open Matrix
namespace PI.WGL.XiU
theorem _root_.solution {N : ℕ} (x : Matrix (Fin N) (Fin N) ℂ) (hx : x ∈ Matrix.unitaryGroup (Fin N) ℂ)
    (w : Fin N → ℂ) : ∑ a, Complex.normSq ((x *ᵥ w) a) = ∑ b, Complex.normSq (w b) := by
  apply Complex.ofReal_injective
  rw [← normSq_sum_eq, ← normSq_sum_eq, Matrix.star_mulVec, ← Matrix.dotProduct_mulVec,
    Matrix.mulVec_mulVec, ← Matrix.star_eq_conjTranspose, (Matrix.mem_unitaryGroup_iff').1 hx,
    Matrix.one_mulVec]
end PI.WGL.XiU
