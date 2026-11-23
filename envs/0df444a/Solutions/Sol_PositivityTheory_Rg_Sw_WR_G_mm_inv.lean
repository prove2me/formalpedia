-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.WR.G.mm_inv
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:54:53.156586+00:00
-- url     : https://prove2.me/submissions/1f2f7ecf-4b0b-4b21-9f9c-a9ed59e475b9

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
namespace PositivityTheory.Rg.Sw.WR.G
theorem _root_.solution (ε : Fin m → Bool) (s : ℝ) (y : E n) (a : Fin m) :
    (GM.Mm ε s (herm y) a)⁻¹ = if ε a then uM (s : ℂ) y else vM (s : ℂ) y := by
  unfold GM.Mm GM.sR uM vM
  split_ifs with h
  · push_cast; rw [mul_one]
  · push_cast
    congr 1
    rw [show Complex.I * ((s : ℂ) * -1) = -(Complex.I * s) by ring, neg_smul, sub_neg_eq_add]
end PositivityTheory.Rg.Sw.WR.G
