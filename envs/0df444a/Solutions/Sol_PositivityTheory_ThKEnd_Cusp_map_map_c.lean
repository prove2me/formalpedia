-- Prove2me | solution 1 for PositivityTheory.ThKEnd.Cusp.map_map_c
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:20:22.245595+00:00
-- url     : https://prove2.me/submissions/7c428682-0bf4-44af-ba0f-ff2b155048ae

import Mathlib
import Definitions.Def_Development_WeilBound_ThetaLifts_EigenvalueEndgame_CuspidalAverages_FirstIdempotentAdjointThird

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
open PositivityTheory PositivityTheory.ThKEnd PositivityTheory.ThKEnd.Cusp
open Matrix
variable {R n ι : Type} [CommRing R] [Fintype n] [DecidableEq n] [Fintype ι] [DecidableEq ι] {c : R →+* R}
  {J x y x' y' : Matrix n n R} {u u' : Matrix n ι R}
namespace PositivityTheory.ThKEnd.Cusp
theorem _root_.solution {a b : Type} (h : ∀ r, c (c r) = r) (z : Matrix a b R) : (z.map c).map c = z := by
  ext i j; exact h _
end PositivityTheory.ThKEnd.Cusp
