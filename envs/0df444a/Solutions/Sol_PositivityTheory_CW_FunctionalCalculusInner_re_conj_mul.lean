-- Prove2me | solution 1 for PositivityTheory.CW.FunctionalCalculusInner.re_conj_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T11:22:30.053768+00:00
-- url     : https://prove2.me/submissions/cd6ba40e-96aa-4bdc-998a-310217eab452

import Definitions.Def_Development_WeilBound_CoreStatements_PublishedTheorems_CasselmanWallach_FunctionalCalculusLaws
import Definitions.Def_Development_WeilBound_CoreStatements_PublishedTheorems_CasselmanWallach_FunctionalCalculusOfBasic

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix Finset ReciprocityTheory.ChartRestriction.DS
open PositivityTheory PositivityTheory.CW
open PositivityTheory.CW.FunctionalCalculusInner
variable {n : ℕ} {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] {ι : Type}
namespace PositivityTheory.CW.FunctionalCalculusInner
theorem _root_.solution (z : ℂ) (r : ℝ) : (starRingEnd ℂ z * ((r : ℂ) * z)).re = r * ‖z‖ ^ 2 := by
  rw [mul_left_comm, Complex.conj_mul']
  norm_cast
end PositivityTheory.CW.FunctionalCalculusInner
