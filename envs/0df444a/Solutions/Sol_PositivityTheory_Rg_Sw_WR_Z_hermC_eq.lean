-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.WR.Z.hermC_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T12:50:55.370707+00:00
-- url     : https://prove2.me/submissions/188d50ad-6ada-42e4-8f02-f70f2c59eed3

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_ClsGainSt
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_ClsGainA
import Theorems.Thm_PositivityTheory_Rg_Sw_WR_Z_ext
import Theorems.Thm_PositivityTheory_Rg_Sw_WR_Z_hermL_apply

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
theorem _root_.solution (w : Fin n → Fin n → ℂ) :
    hermL (fun a b => (w a b).re) + Complex.I • hermL (fun a b => (w a b).im) =
      fun i j => (w i j + w j i) / 2 + Complex.I * (w i j - w j i) / 2 := by
  funext i j
  rw [hermL_apply, hermL_apply]
  show herm (fun a b => (w a b).re) i j + Complex.I * herm (fun a b => (w a b).im) i j = _
  simp only [herm]
  apply Complex.ext <;> simp <;> ring
end PositivityTheory.Rg.Sw.WR.Z
