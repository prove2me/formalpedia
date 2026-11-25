-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.WR.T.cls_shift
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T11:54:44.551158+00:00
-- url     : https://prove2.me/submissions/91d8a394-590c-4339-9fc8-5a52c9721a8c

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_ContinuousHerm
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_ClsShift

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Matrix Filter Topology
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.WR PositivityTheory.Rg.Sw.WR.T
open PositivityTheory.Rg.Sw
namespace PositivityTheory.Rg.Sw.WR.T
theorem _root_.solution {n : ℕ} (s z : ℂ) (p q : ℕ) (R : MvPolynomial (Bool × Fin n × Fin n) ℂ) (y : E n) :
    ((dP y : ℝ) : ℂ) ^ (-z) * cls s 0 p q R y = cls s z p q R y := by
  simp only [cls, neg_zero, Complex.cpow_zero, one_mul]
  ring
end PositivityTheory.Rg.Sw.WR.T
