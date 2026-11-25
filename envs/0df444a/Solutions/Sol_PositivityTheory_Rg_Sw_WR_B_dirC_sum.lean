-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.WR.B.dirC_sum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T11:50:20.118696+00:00
-- url     : https://prove2.me/submissions/eeb69ede-6c32-4135-ad8d-1be22bf8e008

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
theorem _root_.solution {ι : Type} (s : Finset ι) {f : ι → E n → ℂ} {y : E n} (hf : ∀ i, DifferentiableAt ℝ (f i) y)
    (w : Fin n → Fin n → ℂ) : dirC (fun x => ∑ i ∈ s, f i x) w y = ∑ i ∈ s, dirC (f i) w y := by
  have h : HasFDerivAt (fun x => ∑ i ∈ s, f i x) (∑ i ∈ s, fderiv ℝ (f i) y) y := by
    have := HasFDerivAt.sum (u := s) fun i _ => (hf i).hasFDerivAt
    rwa [Finset.sum_fn] at this
  rw [dirC_of h]
  simp only [ContinuousLinearMap.sum_apply, dirC]
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
end PositivityTheory.Rg.Sw.WR.B
