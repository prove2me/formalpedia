-- Prove2me | solution 1 for PI.ScPiBuildW.Loc.LocFrame.hJ_X_left
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T13:37:42.248156+00:00
-- url     : https://prove2.me/submissions/1f478902-8ac0-44e5-b781-1e27501d1495

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_ScPiExists
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TensorFrameConstruction_LocalFramePreservesOrthogonal
import Theorems.Thm_PI_ScPiBuildW_Loc_hJ_span_left

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
theorem _root_.solution {x y : Fin n → ℂ} (hx : x ∈ L.X) (h : ∀ a, hJ ε (L.e a) y = 0) : hJ ε x y = 0 :=
  hJ_span_left ε (S := L.e '' {b | b.1 < r}) hx (by rintro _ ⟨a, _, rfl⟩; exact h a)
end PI.ScPiBuildW.Loc.LocFrame
