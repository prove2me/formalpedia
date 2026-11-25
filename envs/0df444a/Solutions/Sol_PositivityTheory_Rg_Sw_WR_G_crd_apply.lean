-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.WR.G.crd_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T12:01:17.91359+00:00
-- url     : https://prove2.me/submissions/6affb3c5-6303-46e0-b052-5113d29dc292

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_GaussS
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_GWickA
import Theorems.Thm_PositivityTheory_Rg_Sw_WR_G_ent_apply

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
theorem _root_.solution (k : Fin m × Fin n × Bool) (v : Fin m → Fin n → ℂ) :
    crd k v = if k.2.2 then star (v k.1 k.2.1) else v k.1 k.2.1 := by
  unfold crd; split_ifs <;> simp [ent_apply, Complex.conjCLE_apply]
end PositivityTheory.Rg.Sw.WR.G
