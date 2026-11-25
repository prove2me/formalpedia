-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.WR.K.GB.TW.dirC_sum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T11:52:30.197929+00:00
-- url     : https://prove2.me/submissions/5c917246-0c95-437b-8e0b-d86dc3d2a8a5

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
theorem _root_.solution {ι : Type*} (s : Finset ι) {A : ι → E n → ℂ} {y : E n}
    (h : ∀ i ∈ s, DifferentiableAt ℝ (A i) y) (w : Fin n → Fin n → ℂ) :
    dirC (fun x => ∑ i ∈ s, A i x) w y = ∑ i ∈ s, dirC (A i) w y := by
  unfold dirC
  rw [(HasFDerivAt.fun_sum (fun i hi => (h i hi).hasFDerivAt)).fderiv]
  simp only [ContinuousLinearMap.sum_apply]
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
end PositivityTheory.Rg.Sw.WR.K.GB.TW
