-- Prove2me | solution 1 for PositivityTheory.RgUd.TP.Loc.Ptf.xq_pow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T12:03:19.872292+00:00
-- url     : https://prove2.me/submissions/033e6933-018b-4db9-8d95-540111b8e428

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_UnitaryDualProof_TwistedPieces_LocalTraceForms_TraceCompSmulRight
import Theorems.Thm_PositivityTheory_RgUd_TP_Loc_Ptf_xq_mul
import Theorems.Thm_PositivityTheory_RgUd_TP_Loc_Ptf_xq_one

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Module
open PositivityTheory PositivityTheory.RgUd PositivityTheory.RgUd.TP PositivityTheory.RgUd.TP.Loc PositivityTheory.RgUd.TP.Loc.Ptf
variable {R V : Type*} [CommRing R] [AddCommGroup V] [Module R V]
namespace PositivityTheory.RgUd.TP.Loc.Ptf
theorem _root_.solution (I : Ideal R) (x : V →ₗ[R] V) (m : ℕ) : xq I (x ^ m) = xq I x ^ m := by
  induction m with
  | zero => simp [xq_one]
  | succ m ih => rw [pow_succ, xq_mul, ih, pow_succ]
end PositivityTheory.RgUd.TP.Loc.Ptf
