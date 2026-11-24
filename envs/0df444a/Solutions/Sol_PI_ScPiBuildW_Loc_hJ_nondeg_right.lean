-- Prove2me | solution 1 for PI.ScPiBuildW.Loc.hJ_nondeg_right
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T12:57:45.798569+00:00
-- url     : https://prove2.me/submissions/9e1966b5-0c11-4d88-8848-66e7c88a9d3d

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_ScPiExists
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TensorFrameConstruction_LocalFramePreservesOrthogonal
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.HC.Frame.iotaInv_iota
attribute [local simp] Formalism.HC.Frame.iota_iotaInv



set_option autoImplicit false
noncomputable section
open Matrix
open scoped ComplexOrder
open PI PI.ScPiBuildW PI.ScPiBuildW.Loc
open PI.ScPiExists
variable {n : ℕ} (ε : Fin n → Bool)
namespace PI.ScPiBuildW.Loc
theorem _root_.solution (y : Fin n → ℂ) (h : ∀ x, hJ ε x y = 0) : y = 0 := by
  funext i
  have h1 := h (Pi.single i (1 : ℂ))
  have hs : star (Pi.single i (1 : ℂ) : Fin n → ℂ) = (Pi.single i 1 : Fin n → ℂ) := by
    funext j
    by_cases hj : j = i
    · subst hj
      simp
    · simp [Pi.single_apply, hj]
  have e : hJ ε (Pi.single i 1) y = (if ε i then 1 else -1) * y i := by
    first
      | rw [hJ, hs, single_dotProduct, one_mul, Formalism.REAL.Jm, Matrix.mulVec_diagonal]
      | rw [hJ, hs, Matrix.single_dotProduct, one_mul, Formalism.REAL.Jm, Matrix.mulVec_diagonal]
      | simp [hJ, hs, Formalism.REAL.Jm, Matrix.mulVec_diagonal]
  rw [e] at h1
  simp only [Pi.zero_apply]
  split_ifs at h1 <;> simpa using h1
end PI.ScPiBuildW.Loc
