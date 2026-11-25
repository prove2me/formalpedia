-- Prove2me | solution 1 for PositivityTheory.RgUd.TP.Desc.Piece.PDich.Th_rho
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T12:03:41.823949+00:00
-- url     : https://prove2.me/submissions/539d3900-9fe5-4df8-846e-53ec6a7302c4

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_UnitaryDualProof_TwistedPieces_FiniteDimensionalDescent_ClosedOrbitPieces_ToMatrixMulVec
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_UnitaryDualProof_TwistedPieces_FiniteDimensionalDescent_ClosedOrbitPieces_FeIsField
import Theorems.Thm_PositivityTheory_RgUd_TP_Desc_Piece_PDich_Th_mulVec
import Theorems.Thm_GroundTheory_Brauer_SkolemNoether_Twist_of_val
import Theorems.Thm_GroundTheory_Brauer_SkolemNoether_Twist_val_of
import Theorems.Thm_GroundTheory_Brauer_tensorCSA_carrier
import Theorems.Thm_GroundTheory_Brauer_tensorCentralizerAlgEquiv_tmul
import Theorems.Thm_PositivityTheory_RgUd_TP_Desc_Piece_PDich_mat_ext
import Theorems.Thm_PositivityTheory_RgUd_TP_Desc_Piece_PDich_rho_apply
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
variable {k : Type} [Field k] {N : ℕ} {A : Subalgebra k (Matrix (Fin N) (Fin N) k)} {e : Matrix (Fin N) (Fin N) k}
variable (hA : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a) (he : e ∈ A)
namespace PositivityTheory.RgUd.TP.Desc.Piece.PDich
theorem _root_.solution (a : A) : Th e (rho hA he a) = e * a.1 := by
  apply mat_ext; intro v
  rw [Th_mulVec, rho_apply]
  simp [Matrix.mulVecLin_apply, Matrix.mulVec_mulVec, hA _ a.2 _ he]
end PositivityTheory.RgUd.TP.Desc.Piece.PDich
