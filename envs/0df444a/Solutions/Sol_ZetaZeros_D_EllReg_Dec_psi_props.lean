-- Prove2me | solution 1 for ZetaZeros.D.EllReg.Dec.psi_props
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T15:53:10.450125+00:00
-- url     : https://prove2.me/submissions/96c2373a-cc18-4d21-84d4-d41e18ab850d

import Definitions.Def_Formalism_UnipotentAdelicQuotients_EllRegStep
import Definitions.Def_Formalism_UnipotentAdelicQuotients_EllipticRegularity_Decompose

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
open ZetaZeros.D.EllReg.Dec
variable {d : ℕ}
namespace ZetaZeros.D.EllReg.Dec
theorem _root_.solution (x0 : E d) (ψ0 : E d → ℝ) (r : ℝ) (hψ : ContDiff ℝ ∞ ψ0) (hψc : HasCompactSupport ψ0)
    (hψ1 : ∀ y ∈ ball (0 : E d) 1, ψ0 y = 1) (hψs : tsupport ψ0 ⊆ ball 0 2) (hr : 0 < r) :
    ContDiff ℝ ∞ (fun x => ((ψ0 (r⁻¹ • (x - x0)) : ℝ) : ℂ)) ∧
    HasCompactSupport (fun x => ((ψ0 (r⁻¹ • (x - x0)) : ℝ) : ℂ)) ∧
    tsupport (fun x => ((ψ0 (r⁻¹ • (x - x0)) : ℝ) : ℂ)) ⊆ ball x0 (2 * r) ∧
    ∀ x ∈ ball x0 r, ((ψ0 (r⁻¹ • (x - x0)) : ℝ) : ℂ) = 1 := by
  have hcont : Continuous (fun x : E d => r⁻¹ • (x - x0)) :=
    (continuous_id.sub continuous_const).const_smul r⁻¹
  have hnorm : ∀ x : E d, ‖r⁻¹ • (x - x0)‖ = r⁻¹ * dist x x0 := by
    intro x
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hr), dist_eq_norm]
  have h3 : tsupport (fun x => ((ψ0 (r⁻¹ • (x - x0)) : ℝ) : ℂ)) ⊆ ball x0 (2 * r) := by
    have hsub : tsupport (fun x => ((ψ0 (r⁻¹ • (x - x0)) : ℝ) : ℂ)) ⊆
        (fun x : E d => r⁻¹ • (x - x0)) ⁻¹' tsupport ψ0 := by
      apply closure_minimal _ ((isClosed_tsupport ψ0).preimage hcont)
      intro x hx
      apply subset_tsupport
      intro h0
      apply hx
      simp [h0]
    refine hsub.trans fun x hx => ?_
    have h2 : r⁻¹ • (x - x0) ∈ ball (0 : E d) 2 := hψs hx
    rw [mem_ball_zero_iff, hnorm] at h2
    rw [mem_ball]
    calc dist x x0 = r * (r⁻¹ * dist x x0) := by field_simp
      _ < r * 2 := by gcongr
      _ = 2 * r := by ring
  refine ⟨Complex.ofRealCLM.contDiff.comp (hψ.comp ((contDiff_id.sub contDiff_const).const_smul r⁻¹)),
    ?_, h3, ?_⟩
  · exact IsCompact.of_isClosed_subset (isCompact_closedBall x0 (2 * r)) (isClosed_tsupport _)
      (h3.trans ball_subset_closedBall)
  · intro x hx
    have h1 : r⁻¹ • (x - x0) ∈ ball (0 : E d) 1 := by
      rw [mem_ball_zero_iff, hnorm]
      rw [mem_ball] at hx
      calc r⁻¹ * dist x x0 < r⁻¹ * r := by gcongr
        _ = 1 := inv_mul_cancel₀ hr.ne'
    rw [hψ1 _ h1]
    simp
end ZetaZeros.D.EllReg.Dec
