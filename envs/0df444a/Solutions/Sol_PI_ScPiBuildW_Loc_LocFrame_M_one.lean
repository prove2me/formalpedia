-- Prove2me | solution 1 for PI.ScPiBuildW.Loc.LocFrame.M_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T10:19:27.880577+00:00
-- url     : https://prove2.me/submissions/bc4fad2c-ea68-4a11-b52c-bd92e63c9dde

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_ScPiExists
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TensorFrameConstruction_LocalFramePreservesOrthogonal

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
theorem _root_.solution : L.M 1 = 1 := by
  ext a b
  show hJ ε (L.w a) ((1 : Matrix (Fin n) (Fin n) ℂ) *ᵥ L.w b) = (1 : Matrix (Fin k) (Fin k) ℂ) a b
  rw [Matrix.one_mulVec, L.ww, Matrix.one_apply]
end PI.ScPiBuildW.Loc.LocFrame
