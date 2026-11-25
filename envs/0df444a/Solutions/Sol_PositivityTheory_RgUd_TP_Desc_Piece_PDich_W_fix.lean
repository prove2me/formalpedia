-- Prove2me | solution 1 for PositivityTheory.RgUd.TP.Desc.Piece.PDich.W_fix
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T11:55:07.225075+00:00
-- url     : https://prove2.me/submissions/359c57a5-79f8-46bd-b226-802092b3690f

import Mathlib
import Definitions.Def_GroundTheory_Brauer_DoubleCentralizer
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_UnitaryDualProof_TwistedPieces_FiniteDimensionalDescent_ClosedOrbitPieces_ToMatrixMulVec
import Theorems.Thm_GroundTheory_Brauer_SkolemNoether_Twist_of_val
import Theorems.Thm_GroundTheory_Brauer_SkolemNoether_Twist_val_of
import Theorems.Thm_GroundTheory_Brauer_tensorCSA_carrier
import Theorems.Thm_GroundTheory_Brauer_tensorCentralizerAlgEquiv_tmul
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.Brauer.SkolemNoether.Twist.of_val
attribute [local simp] GroundTheory.Brauer.SkolemNoether.Twist.val_of
attribute [local simp] GroundTheory.Brauer.tensorCSA_carrier
attribute [local simp] GroundTheory.Brauer.tensorCentralizerAlgEquiv_tmul



set_option autoImplicit false
noncomputable section
open Matrix
open PositivityTheory PositivityTheory.RgUd PositivityTheory.RgUd.TP PositivityTheory.RgUd.TP.Desc PositivityTheory.RgUd.TP.Desc.Piece PositivityTheory.RgUd.TP.Desc.Piece.PDich
variable {k : Type} [Field k] {N : ℕ}
namespace PositivityTheory.RgUd.TP.Desc.Piece.PDich
theorem _root_.solution {e : Matrix (Fin N) (Fin N) k} (hid : IsIdempotentElem e) {w : Fin N → k} (hw : w ∈ Wd e) :
    e *ᵥ w = w := by
  obtain ⟨v, rfl⟩ := hw
  simp [Matrix.mulVecLin_apply, Matrix.mulVec_mulVec, hid.eq]
end PositivityTheory.RgUd.TP.Desc.Piece.PDich
