-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.WR.B.dirC_comp
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:35:20.003514+00:00
-- url     : https://prove2.me/submissions/a24a1a95-1ab2-4826-a1ff-664ff0c6f259

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
theorem _root_.solution {g : ℂ → ℂ} {g' : ℂ} {f : E n → ℂ} {y : E n} (hg : HasDerivAt g g' (f y))
    (hf : DifferentiableAt ℝ f y) (w : Fin n → Fin n → ℂ) : dirC (fun x => g (f x)) w y = g' * dirC f w y := by
  have h := hg.comp_hasFDerivAt y hf.hasFDerivAt
  rw [show (fun x => g (f x)) = g ∘ f from rfl, dirC_of h, dirC_of hf.hasFDerivAt]
  simp only [ContinuousLinearMap.smul_apply, smul_eq_mul]; ring
end PositivityTheory.Rg.Sw.WR.B
