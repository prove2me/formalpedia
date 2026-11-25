-- Prove2me | solution 1 for PI.ScPiBuildW.Loc.hJ_sub_right
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T10:24:46.833913+00:00
-- url     : https://prove2.me/submissions/c617b6ba-8654-4553-91e2-400a2523747f

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
theorem _root_.solution (x y y' : Fin n → ℂ) : hJ ε x (y - y') = hJ ε x y - hJ ε x y' := by
  first | simp only [hJ, Matrix.mulVec_sub, dotProduct_sub] | simp [hJ, Matrix.mulVec_sub, dotProduct_sub]
end PI.ScPiBuildW.Loc
