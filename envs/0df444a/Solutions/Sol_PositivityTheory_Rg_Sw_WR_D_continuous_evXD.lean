-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.WR.D.continuous_evXD
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T11:54:44.548692+00:00
-- url     : https://prove2.me/submissions/05b9006d-748c-46a0-90b3-6d04cd200488

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_DensDefs
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_DerivFA

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
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.WR PositivityTheory.Rg.Sw.WR.D
open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.WR
variable {m n : ℕ}
namespace PositivityTheory.Rg.Sw.WR.D
theorem _root_.solution (P : PX m n) : Continuous (evX P) := by
  unfold evX
  have h : Continuous fun x : Fin m → Fin n → ℂ =>
      (fun k : Fin m × Fin n × Bool => if k.2.2 then star (x k.1 k.2.1) else x k.1 k.2.1) := by
    refine continuous_pi fun k => ?_
    rcases k with ⟨a, i, b⟩
    cases b
    · simp only [Bool.false_eq_true, ↓reduceIte]
      exact (continuous_apply i).comp (continuous_apply a)
    · simp only [↓reduceIte]
      exact continuous_star.comp ((continuous_apply i).comp (continuous_apply a))
  exact (MvPolynomial.continuous_eval P).comp h
end PositivityTheory.Rg.Sw.WR.D
