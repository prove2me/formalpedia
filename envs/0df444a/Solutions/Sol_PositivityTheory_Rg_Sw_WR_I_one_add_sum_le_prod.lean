-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.WR.I.one_add_sum_le_prod
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T11:51:49.80208+00:00
-- url     : https://prove2.me/submissions/cef90f21-3813-462e-902a-9256911424da

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_ClsBoundAlt
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_Integr

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Matrix
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.WR PositivityTheory.Rg.Sw.WR.I
open PositivityTheory.Rg.Sw
variable {n : ℕ}
namespace PositivityTheory.Rg.Sw.WR.I
theorem _root_.solution (s : Finset (Fin n)) (a : Fin n → ℝ) (ha : ∀ i, 0 ≤ a i) :
    1 + ∑ i ∈ s, a i ≤ ∏ i ∈ s, (1 + a i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert j s hj ih =>
    rw [Finset.sum_insert hj, Finset.prod_insert hj]
    have h0 : 0 ≤ ∑ i ∈ s, a i := Finset.sum_nonneg fun i _ => ha i
    nlinarith [ha j]
end PositivityTheory.Rg.Sw.WR.I
