-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.WR.B.contDiff_det_of
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:35:04.538446+00:00
-- url     : https://prove2.me/submissions/67afc432-8e12-45e4-b9ae-be75a0c97eca

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_ClsBoundA
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_ClsBoundB

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
theorem _root_.solution {M : E n → Matrix (Fin n) (Fin n) ℂ} (h : ∀ a b, ContDiff ℝ (⊤ : ℕ∞) (fun y => M y a b)) :
    ContDiff ℝ (⊤ : ℕ∞) (fun y => (M y).det) := by
  simp_rw [Matrix.det_apply]
  refine ContDiff.sum fun σ _ => ?_
  simp_rw [Units.smul_def, zsmul_eq_mul]
  exact contDiff_const.mul (contDiff_prod fun i _ => h _ _)
end PositivityTheory.Rg.Sw.WR.B
