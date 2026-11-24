-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.WR.G.GM.gramX_isHermitian
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:57:48.453143+00:00
-- url     : https://prove2.me/submissions/b2503b4e-ff58-4aeb-a0ee-217303e49d14

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_GaussS
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_GaussM

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Matrix MvPolynomial
open scoped ComplexOrder
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.WR PositivityTheory.Rg.Sw.WR.G
open PositivityTheory.Rg.Sw
variable {m n : ℕ}
open PositivityTheory.Rg.Sw.WR.G.GM
namespace PositivityTheory.Rg.Sw.WR.G.GM
theorem _root_.solution (ε : Fin m → Bool) (x : Fin m → Fin n → ℂ) : (gramX ε x).IsHermitian := by
  ext i j
  simp only [gramX, Qp, Qb, evX, conjTranspose_apply, map_sub, map_sum, map_mul, eval_X, star_sub, star_sum,
    star_mul', star_star]
  simp only [if_true, Bool.false_eq_true, if_false]
  congr 1 <;> (refine Finset.sum_congr rfl fun a _ => ?_; rw [star_star, mul_comm])
end PositivityTheory.Rg.Sw.WR.G.GM
