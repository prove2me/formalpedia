-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.WR.K.GB.TW.dirC_const_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T11:52:24.358139+00:00
-- url     : https://prove2.me/submissions/ded373eb-3246-4470-a5ae-727dffa5d549

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_Lagr
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_GBTwist

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
open scoped ComplexOrder
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.WR PositivityTheory.Rg.Sw.WR.K PositivityTheory.Rg.Sw.WR.K.GB
open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.WR
open PositivityTheory.Rg.Sw.WR.K.GB.TW
variable {n : ℕ}
namespace PositivityTheory.Rg.Sw.WR.K.GB.TW
theorem _root_.solution {f : E n → ℂ} {y : E n} (hf : DifferentiableAt ℝ f y) (a : ℂ)
    (w : Fin n → Fin n → ℂ) : dirC (fun x => a * f x) w y = a * dirC f w y := by
  unfold dirC
  rw [(hf.hasFDerivAt.const_mul a).fderiv]
  simp only [ContinuousLinearMap.smul_apply, smul_eq_mul]
  ring
end PositivityTheory.Rg.Sw.WR.K.GB.TW
