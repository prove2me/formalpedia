-- Prove2me | solution 1 for PositivityTheory.RgUd.TP.Desc.Piece.PDich.mat_ext
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:31:37.486787+00:00
-- url     : https://prove2.me/submissions/7cb17831-008f-43fd-9a22-46105dc337ec

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
theorem _root_.solution {b b' : Matrix (Fin N) (Fin N) k} (h : ∀ v, b *ᵥ v = b' *ᵥ v) : b = b' :=
  Matrix.toLin'.injective (LinearMap.ext fun v => by simpa [Matrix.toLin'_apply] using h v)
end PositivityTheory.RgUd.TP.Desc.Piece.PDich
