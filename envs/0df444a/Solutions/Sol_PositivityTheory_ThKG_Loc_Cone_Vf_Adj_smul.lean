-- Prove2me | solution 1 for PositivityTheory.ThKG.Loc.Cone.Vf.Adj.smul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-27T05:25:05.38831+00:00
-- url     : https://prove2.me/submissions/facaf292-f57b-4079-91b5-349339b84d39

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_HilbertNinetyQuotientHomEqIff
import Definitions.Def_Development_WeilBound_ThetaLifts_LocalTheory_ConeShifts_ExistsPowIdem
import Theorems.Thm_PositivityTheory_ThKG_Loc_Cone_Vf_mapc_smul

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
theorem _root_.solution {M M' : Matrix β β A} (h : Adj c J M M') {a a' : A} (ha : c a' = a) : Adj c J (a • M) (a' • M') := by
  unfold Adj at *; rw [transpose_smul, Matrix.smul_mul, h, mapc_smul, ha, Matrix.mul_smul]
end Adj
end PositivityTheory.ThKG.Loc.Cone.Vf
