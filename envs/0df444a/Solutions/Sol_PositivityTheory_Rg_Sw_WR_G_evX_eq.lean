-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.WR.G.evX_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T12:08:54.620917+00:00
-- url     : https://prove2.me/submissions/c2ac8fb7-7f97-4820-a533-ec33242cda2c

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_GaussS
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_GWickA
import Theorems.Thm_PositivityTheory_Rg_Sw_WR_G_crd_apply

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
theorem _root_.solution (P : PX m n) (x : Fin m → Fin n → ℂ) : evX P x = MvPolynomial.eval (fun k => crd k x) P := by
  simp only [evX, crd_apply]
end PositivityTheory.Rg.Sw.WR.G
