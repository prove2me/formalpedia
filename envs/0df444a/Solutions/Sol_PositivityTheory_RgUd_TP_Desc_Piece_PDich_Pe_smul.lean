-- Prove2me | solution 1 for PositivityTheory.RgUd.TP.Desc.Piece.PDich.Pe_smul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T11:54:53.297465+00:00
-- url     : https://prove2.me/submissions/72a1fa92-c59f-478c-8ea4-83122bc651c2

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_UnitaryDualProof_TwistedPieces_FiniteDimensionalDescent_ClosedOrbitPieces_FeIsField
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_UnitaryDualProof_TwistedPieces_FiniteDimensionalDescent_ClosedOrbitPieces_PsiMulVec

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
theorem _root_.solution (a : A) (v : Fin N → k) :
    Pe e (a.1 *ᵥ v) = (⟨rho hA he a, a, rfl⟩ : Fe hA he) • Pe e v := by
  apply Subtype.ext
  show e *ᵥ (a.1 *ᵥ v) = a.1 *ᵥ (e *ᵥ v)
  rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hA _ a.2 _ he]
end PositivityTheory.RgUd.TP.Desc.Piece.PDich
