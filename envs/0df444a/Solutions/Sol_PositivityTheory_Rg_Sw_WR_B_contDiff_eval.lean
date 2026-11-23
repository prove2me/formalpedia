-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.WR.B.contDiff_eval
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:53:50.31683+00:00
-- url     : https://prove2.me/submissions/b12761ac-1f84-495f-8d21-92b6e003d04c

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_ClsBoundA
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_ClsBoundB

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
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.WR PositivityTheory.Rg.Sw.WR.B
open PositivityTheory.Rg.Sw
variable {n : ℕ}
namespace PositivityTheory.Rg.Sw.WR.B
theorem _root_.solution {ι : Type} (φ : ι → E n → ℂ) (hφ : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (φ i)) (R : MvPolynomial ι ℂ) :
    ContDiff ℝ (⊤ : ℕ∞) (fun y => MvPolynomial.eval (fun i => φ i y) R) := by
  induction R using MvPolynomial.induction_on with
  | C a => simpa using contDiff_const
  | add p q hp hq => simpa using hp.add hq
  | mul_X p i hp => simpa using hp.mul (hφ i)
end PositivityTheory.Rg.Sw.WR.B
