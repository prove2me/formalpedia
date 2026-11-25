-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_MCPsh_le_circleAverage_of_minorant_4e512974bc58
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T05:10:22.776681+00:00
-- url     : https://prove2.me/submissions/5a0c4814-3f3e-4a69-b84b-3c7a349f5a16

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_PshCore
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_MCPsh_log_norm_le_circleAverage_2cf1c0064d60
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_MCPsh_circleIntegrable_log_norm_of_analytic_63c35a4f4a91

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.MCPsh
open Metric Filter Real
noncomputable section
namespace GroundTheory.Heights₂.Heights.MCPsh
theorem _root_.solution {φ ℓ : ℂ → ℝ} {h : ℂ → ℂ} {ℓ0 : ℝ}
    (hh : AnalyticOnNhd ℂ h (closedBall 0 1)) (h0 : h 0 ≠ 0)
    (hφ : CircleIntegrable φ 0 1) (hℓ : CircleIntegrable ℓ 0 1)
    (hpt : ∀ ζ ∈ sphere (0:ℂ) 1, h ζ ≠ 0 → 2 * Real.log ‖h ζ‖ - ℓ ζ ≤ φ ζ)
    (hℓavg : circleAverage ℓ 0 1 ≤ ℓ0) (hφ0 : φ 0 ≤ 2 * Real.log ‖h 0‖ - ℓ0) :
    φ 0 ≤ circleAverage φ 0 1 := by
  have hlog := circleIntegrable_log_norm_of_analytic hh
  have hj := log_norm_le_circleAverage hh h0
  set ψ : ℂ → ℝ := fun ζ => 2 * Real.log ‖h ζ‖ - ℓ ζ with hψdef
  have h2 : CircleIntegrable (fun ζ => (2:ℝ) • Real.log ‖h ζ‖) 0 1 := hlog.const_fun_smul
  have hψ : CircleIntegrable ψ 0 1 := by
    have := h2.fun_sub hℓ
    simpa [ψ, smul_eq_mul] using this
  have havgψ : circleAverage ψ 0 1 = 2 * circleAverage (fun ζ => Real.log ‖h ζ‖) 0 1 -
      circleAverage ℓ 0 1 := by
    have := circleAverage_fun_sub h2 hℓ
    simp only [smul_eq_mul] at this
    rw [show ψ = fun ζ => 2 * Real.log ‖h ζ‖ - ℓ ζ from rfl, this]
    congr 1
    have := circleAverage_fun_smul (c := (0:ℂ)) (R := 1) (a := (2:ℝ)) (f := fun ζ => Real.log ‖h ζ‖)
    simpa [smul_eq_mul] using this
  have hzeros : h ⁻¹' {0}ᶜ ∈ codiscreteWithin (sphere (0:ℂ) |(1:ℝ)|) := by
    have hconn : IsConnected (closedBall (0:ℂ) 1) :=
      ⟨⟨0, mem_closedBall_self zero_le_one⟩, (convex_closedBall (0:ℂ) 1).isPreconnected⟩
    have := hh.preimage_zero_mem_codiscreteWithin h0 (mem_closedBall_self zero_le_one) hconn
    exact codiscreteWithin_mono (by simpa using sphere_subset_closedBall) this
  have heq : (fun ζ => φ ζ - ψ ζ) =ᶠ[codiscreteWithin (sphere (0:ℂ) |(1:ℝ)|)]
      (fun ζ => max (φ ζ - ψ ζ) 0) := by
    have hs : sphere (0:ℂ) |(1:ℝ)| ∈ codiscreteWithin (sphere (0:ℂ) |(1:ℝ)|) :=
      self_mem_codiscreteWithin _
    filter_upwards [hzeros, hs] with ζ hζ hζs
    have hζs' : ζ ∈ sphere (0:ℂ) 1 := by simpa using hζs
    have := hpt ζ hζs' hζ
    rw [max_eq_left (by simp only [ψ]; linarith)]
  have hnn : 0 ≤ circleAverage (fun ζ => φ ζ - ψ ζ) 0 1 := by
    rw [circleAverage_congr_codiscreteWithin heq one_ne_zero]
    exact circleAverage_nonneg_of_nonneg fun ζ _ => le_max_right _ _
  rw [circleAverage_fun_sub hφ hψ, havgψ] at hnn
  linarith
end GroundTheory.Heights₂.Heights.MCPsh
