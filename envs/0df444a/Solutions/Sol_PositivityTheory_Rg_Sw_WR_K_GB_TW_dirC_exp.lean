-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.WR.K.GB.TW.dirC_exp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T11:52:26.61046+00:00
-- url     : https://prove2.me/submissions/4b4f38b4-3b40-49ad-b413-327728c64031

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
theorem _root_.solution {g : E n → ℂ} {y : E n} (hg : DifferentiableAt ℝ g y) (w : Fin n → Fin n → ℂ) :
    dirC (fun x => Complex.exp (g x)) w y = Complex.exp (g y) * dirC g w y := by
  unfold dirC
  rw [hg.hasFDerivAt.cexp.fderiv]
  simp only [ContinuousLinearMap.smul_apply, smul_eq_mul]
  ring
end PositivityTheory.Rg.Sw.WR.K.GB.TW
