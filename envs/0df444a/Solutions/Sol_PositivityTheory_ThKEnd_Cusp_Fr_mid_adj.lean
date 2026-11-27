-- Prove2me | solution 1 for PositivityTheory.ThKEnd.Cusp.Fr.mid_adj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-27T05:22:23.561805+00:00
-- url     : https://prove2.me/submissions/4b9972db-26fd-4832-adfe-00899cc15571

import Mathlib
import Definitions.Def_Development_WeilBound_ThetaLifts_EigenvalueEndgame_CuspidalAverages_FirstIdempotentAdjointThird
import Theorems.Thm_PositivityTheory_ThKEnd_Cusp_Adj_one
import Theorems.Thm_PositivityTheory_ThKEnd_Cusp_Adj_add
import Theorems.Thm_PositivityTheory_ThKEnd_Cusp_Adj_sub
import Theorems.Thm_PositivityTheory_ThKEnd_Cusp_Adj_mul
import Theorems.Thm_PositivityTheory_ThKEnd_Cusp_Fr_first_idempotent_adjoint_third
import Theorems.Thm_PositivityTheory_ThKEnd_Cusp_Fr_third_idempotent_adjoint_first

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
theorem _root_.solution {s s' : Matrix n n R} (hs : Adj c J s s') : Adj c J (mid c J u u' s) (mid c J u u' s') := by
  have q := (Adj.one.sub h.first_idempotent_adjoint_third).sub h.third_idempotent_adjoint_first
  have := (h.first_idempotent_adjoint_third.add ((q.mul hs).mul q)).add h.third_idempotent_adjoint_first
  rw [sub_right_comm 1 (e3 c J u u'), ← Matrix.mul_assoc] at this
  rw [show mid c J u u' s' = e3 c J u u' + (1 - e1 c J u u' - e3 c J u u') * s' * (1 - e1 c J u u' - e3 c J u u') + e1 c J u u' by
    rw [mid]; abel]
  exact this
end PositivityTheory.ThKEnd.Cusp.Fr
