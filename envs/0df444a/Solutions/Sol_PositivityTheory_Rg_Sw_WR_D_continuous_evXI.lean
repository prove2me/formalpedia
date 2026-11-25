-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.WR.D.continuous_evXI
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T11:52:15.661489+00:00
-- url     : https://prove2.me/submissions/9001b7be-c64f-4a66-80ea-6ea2503779ce

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_DensDefs
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_ImportsBisMore
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_ContinuousEvXI

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
theorem _root_.solution (P : PX m n) : Continuous fun x : Fin m → Fin n → ℂ => evX P x := by
  unfold evX
  have hg : Continuous fun x : Fin m → Fin n → ℂ =>
      (fun k : Fin m × Fin n × Bool => if k.2.2 then star (x k.1 k.2.1) else x k.1 k.2.1) := by
    refine continuous_pi fun k => ?_
    by_cases h : k.2.2
    · simp only [h, if_true]
      exact continuous_star.comp ((continuous_apply _).comp (continuous_apply _))
    · simp only [h, if_false, Bool.false_eq_true]
      exact (continuous_apply _).comp (continuous_apply _)
  exact (MvPolynomial.continuous_eval P).comp hg
end PositivityTheory.Rg.Sw.WR.D
