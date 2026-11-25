-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.WR.D.gramX_star
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T11:52:30.253106+00:00
-- url     : https://prove2.me/submissions/95564424-5be4-4c39-8916-d3b655614c2d

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_DensDefs
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_ContinuousEvX

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.WR PositivityTheory.Rg.Sw.WR.D
open PositivityTheory.Rg.Sw
variable {m n : ℕ}
namespace PositivityTheory.Rg.Sw.WR.D
theorem _root_.solution (ε : Fin m → Bool) (x : Fin m → Fin n → ℂ) (i j : Fin n) :
    star (gramX ε x i j) = gramX ε x j i := by
  simp only [gramX, Qp, Qb, evX, map_sub, map_sum, map_mul, MvPolynomial.eval_X, ↓reduceIte,
    Bool.false_eq_true, star_sub, star_sum, star_mul, star_star]
end PositivityTheory.Rg.Sw.WR.D
