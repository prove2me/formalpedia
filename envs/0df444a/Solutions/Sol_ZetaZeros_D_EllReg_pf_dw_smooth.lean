-- Prove2me | solution 1 for ZetaZeros.D.EllReg.pf_dw_smooth
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:39:37.279834+00:00
-- url     : https://prove2.me/submissions/67d9f1ad-cee9-4756-a3fc-fa3585eaa92c

import Definitions.Def_Formalism_UnipotentAdelicQuotients_EllRegCut
import Definitions.Def_Formalism_UnipotentAdelicQuotients_EllipticRegularity_PairingFourier
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
namespace ZetaZeros.D.EllReg
open MeasureTheory Metric Filter Topology
open scoped ContDiff FourierTransform ENNReal
noncomputable section
variable {d : ℕ}
private theorem contDiff_infty_fderiv_of_contDiff_infty {f : E d → ℂ} (hf : ContDiff ℝ ∞ f) : ContDiff ℝ ∞ (fderiv ℝ f) := by
  exact (contDiff_infty_iff_fderiv.1 hf).2
end
end ZetaZeros.D.EllReg
end

set_option autoImplicit false
open ZetaZeros ZetaZeros.D ZetaZeros.D.EllReg
open MeasureTheory Metric Filter Topology
open scoped ContDiff FourierTransform ENNReal
noncomputable section
variable {d : ℕ}
namespace ZetaZeros.D.EllReg
theorem _root_.solution (L : List (Fin d)) (k : E d → ℂ) (hk : ContDiff ℝ ∞ k) (hkc : HasCompactSupport k) :
    ContDiff ℝ ∞ (dw L k) ∧ HasCompactSupport (dw L k) := by
  induction L with
  | nil => exact ⟨hk, hkc⟩
  | cons j w ih =>
    obtain ⟨h1, h2⟩ := ih
    refine ⟨?_, ?_⟩
    · show ContDiff ℝ ∞ (fun x => fderiv ℝ (dw w k) x (ev j))
      exact (contDiff_infty_fderiv_of_contDiff_infty h1).clm_apply contDiff_const
    · show HasCompactSupport (fun x => fderiv ℝ (dw w k) x (ev j))
      refine (h2.fderiv ℝ).mono ?_
      intro x hx
      simp only [Function.mem_support] at hx ⊢
      intro h0
      apply hx
      rw [h0]
      simp
end ZetaZeros.D.EllReg
