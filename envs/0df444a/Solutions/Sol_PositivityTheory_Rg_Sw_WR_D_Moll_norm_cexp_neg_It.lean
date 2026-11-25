-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.WR.D.Moll.norm_cexp_neg_It
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T11:50:57.526336+00:00
-- url     : https://prove2.me/submissions/f333acfe-1dcb-4d6f-b688-adbcfd5b97bd

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_MollIdA
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_MollId

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.WR PositivityTheory.Rg.Sw.WR.D PositivityTheory.Rg.Sw.WR.D.Moll
open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.WR PositivityTheory.Rg.Sw.WR.D
variable {n : ℕ}
namespace PositivityTheory.Rg.Sw.WR.D.Moll
theorem _root_.solution (t r : ℝ) : ‖Complex.exp (-(Complex.I * t * r))‖ = 1 := by
  have : -(Complex.I * (t : ℂ) * (r : ℂ)) = ((-(t * r) : ℝ) : ℂ) * Complex.I := by push_cast; ring
  rw [this, Complex.norm_exp_ofReal_mul_I]
end PositivityTheory.Rg.Sw.WR.D.Moll
