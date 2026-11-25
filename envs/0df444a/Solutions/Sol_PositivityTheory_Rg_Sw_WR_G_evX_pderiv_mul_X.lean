-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.WR.G.evX_pderiv_mul_X
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T12:23:00.827813+00:00
-- url     : https://prove2.me/submissions/bb3fb8d0-076e-43d7-b56b-bbcfebbd23fc

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_GaussS
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_GWickA
import Theorems.Thm_PositivityTheory_Rg_Sw_WR_G_evX_eq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Matrix MvPolynomial
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.WR PositivityTheory.Rg.Sw.WR.G
open PositivityTheory.Rg.Sw
variable {m n : ℕ}
namespace PositivityTheory.Rg.Sw.WR.G
theorem _root_.solution (p : PX m n) (k b : Fin m × Fin n × Bool) (x : Fin m → Fin n → ℂ) :
    evX (pderiv b (p * X k)) x = evX (pderiv b p) x * crd k x + evX p x * (if k = b then 1 else 0) := by
  rw [pderiv_mul, pderiv_X]
  by_cases h : k = b
  · subst h; simp [evX_eq]
  · simp [evX_eq, Pi.single_apply, h]
end PositivityTheory.Rg.Sw.WR.G
