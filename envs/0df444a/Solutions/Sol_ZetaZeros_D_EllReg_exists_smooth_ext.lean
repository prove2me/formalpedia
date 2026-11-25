-- Prove2me | solution 1 for ZetaZeros.D.EllReg.exists_smooth_ext
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T16:00:22.494184+00:00
-- url     : https://prove2.me/submissions/b008f171-35ee-4627-8033-f2d8112bf4e2

import Definitions.Def_Formalism_UnipotentAdelicQuotients_EllipticRegularity_KernDecay
import Definitions.Def_Formalism_UnipotentAdelicQuotients_EllipticRegularity_KernDil
import Definitions.Def_Formalism_UnipotentAdelicQuotients_EllipticRegularity_KernDer
import Definitions.Def_Formalism_UnipotentAdelicQuotients_EllipticRegularity_ExistsSmoothExt

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ZetaZeros ZetaZeros.D ZetaZeros.D.EllReg
open MeasureTheory Metric Filter Topology
open scoped ContDiff FourierTransform ENNReal
noncomputable section
namespace ZetaZeros.D.EllReg
theorem _root_.solution {d : ℕ} {U : Set (E d)} {a : E d → ℂ} {x0 : E d} (hU : IsOpen U) (hx0 : x0 ∈ U)
    (ha : ContDiffOn ℝ ∞ a U) :
    ∃ r0 > 0, ball x0 (2 * r0) ⊆ U ∧ ∃ b : E d → ℂ, ContDiff ℝ ∞ b ∧ HasCompactSupport b ∧
      ∀ x ∈ closedBall x0 (2 * r0), b x = a x := by
  obtain ⟨R, hR, hRU⟩ := Metric.isOpen_iff.1 hU x0 hx0
  let χ : ContDiffBump x0 := ⟨R / 2, 3 * R / 4, by positivity, by linarith⟩
  refine ⟨R / 4, by positivity, ?_, fun x => ((χ x : ℝ) : ℂ) * a x, ?_, ?_, ?_⟩
  · exact (Metric.ball_subset_ball (by linarith)).trans hRU
  · have hsub : tsupport χ ⊆ U := by
      rw [χ.tsupport_eq]
      exact (Metric.closedBall_subset_ball (by show 3 * R / 4 < R; linarith)).trans hRU
    refine contDiff_iff_contDiffAt.2 fun x => ?_
    by_cases hx : x ∈ U
    · exact ((Complex.ofRealCLM.contDiff.comp χ.contDiff).contDiffAt).mul
        ((ha x hx).contDiffAt (hU.mem_nhds hx))
    · have hx' : x ∉ tsupport χ := fun h => hx (hsub h)
      have hev : (fun x => ((χ x : ℝ) : ℂ) * a x) =ᶠ[nhds x] fun _ => 0 := by
        filter_upwards [notMem_tsupport_iff_eventuallyEq.1 hx'] with y hy
        simp [hy]
      exact contDiffAt_const.congr_of_eventuallyEq hev
  · exact (χ.hasCompactSupport.comp_left Complex.ofReal_zero).mul_right
  · intro x hx
    have hx' : x ∈ Metric.closedBall x0 χ.rIn := by
      show x ∈ Metric.closedBall x0 (R / 2)
      exact Metric.closedBall_subset_closedBall (by linarith) hx
    simp [χ.one_of_mem_closedBall hx']
end ZetaZeros.D.EllReg
