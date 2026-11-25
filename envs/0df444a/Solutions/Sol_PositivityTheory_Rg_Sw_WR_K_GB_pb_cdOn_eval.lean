-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.WR.K.GB.pb_cdOn_eval
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T11:53:10.256262+00:00
-- url     : https://prove2.me/submissions/68f51d17-3576-40c2-946e-fa7ef5a7d39c

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_ClsGainBSt
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_GBBound

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
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.WR PositivityTheory.Rg.Sw.WR.K PositivityTheory.Rg.Sw.WR.K.GB
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {n : ℕ}
namespace PositivityTheory.Rg.Sw.WR.K.GB
theorem _root_.solution {ι : Type} (R : MvPolynomial ι ℂ) (v : ι → Mc n → ℂ) (s : Set (Mc n))
    (hv : ∀ k, ContDiffOn ℂ (⊤ : ℕ∞) (v k) s) :
    ContDiffOn ℂ (⊤ : ℕ∞) (fun b => MvPolynomial.eval (fun k => v k b) R) s := by
  induction R using MvPolynomial.induction_on with
  | C a => simpa using (contDiffOn_const : ContDiffOn ℂ (⊤ : ℕ∞) (fun _ : Mc n => a) s)
  | add p q hp hq => simpa using hp.add hq
  | mul_X p k hp => simpa using hp.mul (hv k)
end PositivityTheory.Rg.Sw.WR.K.GB
