-- Prove2me | solution 1 for PositivityTheory.ThKG.Loc.Cone.Vf.Adj.mul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:59:10.945811+00:00
-- url     : https://prove2.me/submissions/b24d061f-585b-46da-b76a-d6ee850abfe5

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
theorem _root_.solution {M M' N N' : Matrix β β A} (h : Adj c J M M') (h' : Adj c J N N') : Adj c J (M * N) (N' * M') := by
  unfold Adj at *
  rw [transpose_mul, Matrix.mul_assoc, h, ← Matrix.mul_assoc, h', mapc_mul, Matrix.mul_assoc]
end Adj
end PositivityTheory.ThKG.Loc.Cone.Vf
