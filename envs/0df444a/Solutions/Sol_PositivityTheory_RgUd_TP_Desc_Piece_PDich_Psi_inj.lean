-- Prove2me | solution 1 for PositivityTheory.RgUd.TP.Desc.Piece.PDich.Psi_inj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T11:54:56.559144+00:00
-- url     : https://prove2.me/submissions/3a94f870-a533-4725-a95a-ea73da1d13ac

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_UnitaryDualProof_TwistedPieces_FiniteDimensionalDescent_ClosedOrbitPieces_FeIsField
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_UnitaryDualProof_TwistedPieces_FiniteDimensionalDescent_ClosedOrbitPieces_PsiMulVec
import Theorems.Thm_PositivityTheory_RgUd_TP_Desc_Piece_PDich_Th_inj


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
open PositivityTheory PositivityTheory.RgUd PositivityTheory.RgUd.TP PositivityTheory.RgUd.TP.Desc PositivityTheory.RgUd.TP.Desc.Piece PositivityTheory.RgUd.TP.Desc.Piece.PDich
variable {k : Type} [Field k] {N : ℕ} {A : Subalgebra k (Matrix (Fin N) (Fin N) k)} {e : Matrix (Fin N) (Fin N) k}
  (hA : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a) (he : e ∈ A)
namespace PositivityTheory.RgUd.TP.Desc.Piece.PDich
theorem _root_.solution : Function.Injective (Psi hA he) := by
  intro f g h
  have := Th_inj h
  ext w : 1
  exact congrArg (fun F : Module.End k (Wd e) => F w) this
end PositivityTheory.RgUd.TP.Desc.Piece.PDich
