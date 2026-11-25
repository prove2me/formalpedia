-- Prove2me | solution 1 for PI.ScPiBuildW.Loc.LocFrame.spanLt_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T10:24:41.30495+00:00
-- url     : https://prove2.me/submissions/40d4e588-f1de-4405-8ce8-c98a2d4ae53f

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
theorem _root_.solution (a : ℕ) (ha : a ≤ r) : spanLt L.e a ≤ L.X :=
  Submodule.span_mono (Set.image_mono fun b _ => b.isLt)
end PI.ScPiBuildW.Loc.LocFrame
