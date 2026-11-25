-- Prove2me | solution 1 for PositivityTheory.ThKG.Loc.Cone.Vf.Adj.sub
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T12:01:45.346258+00:00
-- url     : https://prove2.me/submissions/acae7ea2-31ce-4cae-85cd-c0901718a62e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_HilbertNinetyQuotientHomEqIff
import Definitions.Def_Development_WeilBound_ThetaLifts_LocalTheory_ConeShifts_ExistsPowIdem

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PositivityTheory PositivityTheory.ThKG PositivityTheory.ThKG.Loc PositivityTheory.ThKG.Loc.Cone PositivityTheory.ThKG.Loc.Cone.Vf
open Matrix GlobalTheory.WeilM
variable {R A β : Type} [CommRing R] [CommRing A] [Algebra R A] (c : A →ₐ[R] A) [Fintype β] [DecidableEq β]
variable {c} {J : Matrix β β A}
namespace PositivityTheory.ThKG.Loc.Cone.Vf
namespace Adj
theorem _root_.solution {M M' N N' : Matrix β β A} (h : Adj c J M M') (h' : Adj c J N N') : Adj c J (M - N) (M' - N') := by
  unfold Adj at *; rw [transpose_sub, Matrix.sub_mul, h, h', mapc_sub, Matrix.mul_sub]
end Adj
end PositivityTheory.ThKG.Loc.Cone.Vf
