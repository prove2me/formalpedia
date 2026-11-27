-- Prove2me | solution 1 for PositivityTheory.ThKG.Loc.Cone.Vf.Adj.pow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-27T05:23:50.660872+00:00
-- url     : https://prove2.me/submissions/cd9d7fbf-37d5-4af6-bd72-7172779594e4

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_HilbertNinetyQuotientHomEqIff
import Definitions.Def_Development_WeilBound_ThetaLifts_LocalTheory_ConeShifts_ExistsPowIdem
import Theorems.Thm_PositivityTheory_ThKG_Loc_Cone_Vf_Adj_one
import Theorems.Thm_PositivityTheory_ThKG_Loc_Cone_Vf_Adj_mul

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
theorem _root_.solution {M : Matrix β β A} (h : Adj c J M M) (N : ℕ) : Adj c J (M ^ N) (M ^ N) := by
  induction N with
  | zero => simpa using Adj.one
  | succ N ih => have := ih.mul h; rwa [← pow_succ, ← pow_succ'] at this
end Adj
end PositivityTheory.ThKG.Loc.Cone.Vf
