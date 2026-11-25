-- Prove2me | solution 1 for PI.ScPiBuildW.Loc.LocFrame.hJ_X_right
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T10:48:41.311024+00:00
-- url     : https://prove2.me/submissions/9d960c9f-b44c-4720-945f-e605840c0b5f

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_ScPiExists
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TensorFrameConstruction_LocalFramePreservesOrthogonal
import Theorems.Thm_PI_ScPiBuildW_Loc_hJ_span_right

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix
open scoped ComplexOrder
open PI PI.ScPiBuildW PI.ScPiBuildW.Loc
open PI.ScPiExists
open PI.ScPiBuildW.Loc.LocFrame
variable {n r k : ℕ} {ε : Fin n → Bool} (L : LocFrame n r k ε)
namespace PI.ScPiBuildW.Loc.LocFrame
theorem _root_.solution {x y : Fin n → ℂ} (hx : x ∈ L.X) (h : ∀ a, hJ ε y (L.e a) = 0) : hJ ε y x = 0 :=
  hJ_span_right ε (S := L.e '' {b | b.1 < r}) hx (by rintro _ ⟨a, _, rfl⟩; exact h a)
end PI.ScPiBuildW.Loc.LocFrame
