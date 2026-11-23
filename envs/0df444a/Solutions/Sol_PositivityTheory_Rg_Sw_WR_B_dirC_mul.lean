-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.WR.B.dirC_mul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:33:13.736847+00:00
-- url     : https://prove2.me/submissions/d1d47395-f43e-4c50-b57f-230d4ae9d3d2

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_ClsBoundA
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_ClsBoundB
import Theorems.Thm_PositivityTheory_Rg_Sw_WR_B_dirC_of

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
theorem _root_.solution {f g : E n → ℂ} {y : E n} (hf : DifferentiableAt ℝ f y) (hg : DifferentiableAt ℝ g y)
    (w : Fin n → Fin n → ℂ) : dirC (fun x => f x * g x) w y = f y * dirC g w y + g y * dirC f w y := by
  have h : HasFDerivAt (fun x => f x * g x) _ y := hf.hasFDerivAt.mul hg.hasFDerivAt
  rw [dirC_of h, dirC_of hf.hasFDerivAt, dirC_of hg.hasFDerivAt]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]; ring
end PositivityTheory.Rg.Sw.WR.B
