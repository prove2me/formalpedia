-- Prove2me | solution 1 for PositivityTheory.ThKEnd.Two.embM_mul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:57:51.857817+00:00
-- url     : https://prove2.me/submissions/6df74b99-2538-4ec4-a384-fd405143f5a0

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_HilbertNinetyQuotientHomEqIff
import Definitions.Def_Development_WeilBound_ThetaLifts_EigenvalueEndgame_SignatureSplitting_EmbMMul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
set_option linter.unusedSectionVars false
open PositivityTheory PositivityTheory.ThKEnd PositivityTheory.ThKEnd.Two
open Matrix GlobalTheory.WeilM
variable {S R d k : Type} [CommRing S] [CommRing R] [Algebra S R] [Fintype d] [DecidableEq d] [Fintype k] [DecidableEq k]
variable {c : R →ₐ[S] R} {J : Matrix d d R} {X Y : Matrix d k R}
namespace PositivityTheory.ThKEnd.Two
theorem _root_.solution {e : Type} (g g' : Matrix k k R) (T : Matrix d e R) :
    embM c J X Y g g' * T = T + X * (g - 1) * (Tᵀ * J * Y.map c)ᵀ - Y * (g' - 1) * (Tᵀ * J * X.map c)ᵀ := by
  simp only [embM, Matrix.sub_mul, Matrix.add_mul, Matrix.one_mul, Matrix.mul_assoc, tr_mul]
end PositivityTheory.ThKEnd.Two
