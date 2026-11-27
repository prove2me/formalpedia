-- Prove2me | solution 1 for PositivityTheory.ThKEnd.Cusp.Fr.lv_adj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-27T05:22:12.847786+00:00
-- url     : https://prove2.me/submissions/0cb56c1e-2adf-4009-880d-20d2fdd4453d

import Mathlib
import Definitions.Def_Development_WeilBound_ThetaLifts_EigenvalueEndgame_CuspidalAverages_FirstIdempotentAdjointThird
import Theorems.Thm_PositivityTheory_ThKEnd_Cusp_Adj_one
import Theorems.Thm_PositivityTheory_ThKEnd_Cusp_Adj_add
import Theorems.Thm_PositivityTheory_ThKEnd_Cusp_Adj_sub
import Theorems.Thm_PositivityTheory_ThKEnd_Cusp_Fr_adj

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
open PositivityTheory.ThKEnd.Cusp.Fr
variable (h : Fr c J u u')
include h
namespace PositivityTheory.ThKEnd.Cusp.Fr
theorem _root_.solution (g g' : Matrix ι ι R) : Adj c J (lv c J u u' g g') (lv c J u u' (g'.map c)ᵀ (g.map c)ᵀ) := by
  have e : ∀ g : Matrix ι ι R, ((g - 1).map c)ᵀ = (g.map c)ᵀ - 1 := fun g => by
    rw [Matrix.map_sub _ (map_sub c), Matrix.map_one _ (map_zero c) (map_one c), transpose_sub, transpose_one]
  have := (Adj.one.add (h.adj u u' (g - 1))).sub (h.adj u' u (g' - 1))
  rw [e, e] at this
  rw [show lv c J u u' (g'.map c)ᵀ (g.map c)ᵀ = 1 + -(u' * ((g.map c)ᵀ - 1) * row c J u) - -(u * ((g'.map c)ᵀ - 1) * row c J u') by
    rw [lv]; abel]
  exact this
end PositivityTheory.ThKEnd.Cusp.Fr
