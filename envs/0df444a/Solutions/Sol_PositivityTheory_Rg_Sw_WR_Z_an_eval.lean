-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.WR.Z.an_eval
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:57:48.769681+00:00
-- url     : https://prove2.me/submissions/be076968-e21b-40e4-aa4b-025d9e6b83e9

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_ClsGainSt
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_ClsGainA

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.WR PositivityTheory.Rg.Sw.WR.Z
variable {n : ℕ}
namespace PositivityTheory.Rg.Sw.WR.Z
theorem _root_.solution {ι : Type} (f : ι → MC n → ℂ) (B₀ : MC n) (hf : ∀ k, AnalyticAt ℂ (f k) B₀)
    (R : MvPolynomial ι ℂ) : AnalyticAt ℂ (fun B => MvPolynomial.eval (fun k => f k B) R) B₀ := by
  induction R using MvPolynomial.induction_on with
  | C a => simpa using analyticAt_const
  | add p q hp hq =>
    simp only [map_add]
    exact hp.add hq
  | mul_X p k hp =>
    simp only [map_mul, MvPolynomial.eval_X]
    exact hp.mul (hf k)
end PositivityTheory.Rg.Sw.WR.Z
