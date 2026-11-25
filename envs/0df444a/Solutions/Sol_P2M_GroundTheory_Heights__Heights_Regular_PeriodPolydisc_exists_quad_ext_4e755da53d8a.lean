-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Regular_PeriodPolydisc_exists_quad_ext_4e755da53d8a
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T08:26:38.805667+00:00
-- url     : https://prove2.me/submissions/2aab9641-2129-410d-9372-765c367f1043

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Regularisation_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Regularisation_PosSemidefOfIntQuadNonneg
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Regular_exists_analytic_log_14266ed031aa
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Regular_eqOn_of_exp_eq_35ecbbb8e43f
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Regular_isOpen_logCover_5a352f02a4d1
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Regular_convex_logCover_7e1cb67a0f5e
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Regular_logCover_nonempty_2f09675a86df
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Regular_continuous_expCover_267707a2e3fe
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Regular_expCover_mem_ball_a7e28df76d18
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Regular_PeriodPolydisc_exp_quadratic_tau_shifted_d0d1d6cc101f

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Regular
open Metric Matrix Topology Filter
noncomputable section
open GroundTheory.Heights₂.Heights.Regular.PeriodPolydisc
variable {n a g : ℕ} (P : PeriodPolydisc n a g)
namespace GroundTheory.Heights₂.Heights.Regular.PeriodPolydisc
theorem _root_.solution (h0 : ExpQuadMonomial.Statement) (v : Fin g → ℤ) :
    ∃ Q : (Fin n → ℂ) → ℂ, AnalyticOnNhd ℂ Q (ball 0 1) ∧ ∀ w ∈ logCover P.a_le,
      Q (expCover a w) = (fun k => (v k : ℂ)) ⬝ᵥ P.tau0 w *ᵥ fun k => (v k : ℂ) := by
  obtain ⟨hnn, h, hha, hh0, hhe⟩ := h0 n a g P v
  obtain ⟨G, hGa, hGe⟩ := exists_analytic_log isOpen_ball (convex_ball 0 1)
    ⟨0, mem_ball_self one_pos⟩ hha hh0
  set F : (Fin n → ℂ) → ℂ := fun w =>
    2 * Real.pi * Complex.I * ((fun k => (v k : ℂ)) ⬝ᵥ P.tau0 w *ᵥ fun k => (v k : ℂ)) with hFdef
  have hFe : ∀ w ∈ logCover P.a_le, Complex.exp (F w) = h (expCover a w) := fun w hw =>
    P.exp_quadratic_tau_shifted v hnn h w (hhe w hw)
  have hent : ∀ p q, ContinuousOn (fun w => P.tau0 w p q) (logCover P.a_le) := fun p q => by
    have : (fun w => P.tau0 w p q) = fun w => P.τ w p q - ∑ i : Fin a,
        w (Fin.castLE P.a_le i) / (2 * Real.pi * Complex.I) * ((P.B i p q : ℤ) : ℂ) := by
      funext w
      simp [tau0, Matrix.sum_apply]
    rw [this]
    exact (P.analytic p q).continuousOn.sub (continuousOn_finsetSum _ fun i _ =>
      (((continuous_apply _).continuousOn).div_const _).mul continuousOn_const)
  have hFc : ContinuousOn F (logCover P.a_le) := by
    simp only [hFdef, dotProduct, mulVec]
    exact continuousOn_const.mul (continuousOn_finsetSum _ fun p _ => continuousOn_const.mul
      (continuousOn_finsetSum _ fun q _ => (hent p q).mul continuousOn_const))
  have hmaps : Set.MapsTo (expCover a) (logCover P.a_le) (ball 0 1) := fun w hw =>
    expCover_mem_ball P.a_le hw
  obtain ⟨w₀, hw₀⟩ := logCover_nonempty P.a_le
  set c := F w₀ - G (expCover a w₀) with hc
  have hGc : ContinuousOn (fun w => G (expCover a w) + c) (logCover P.a_le) :=
    (hGa.continuousOn.comp (continuous_expCover a).continuousOn hmaps).add continuousOn_const
  have key := eqOn_of_exp_eq (isOpen_logCover P.a_le) (convex_logCover P.a_le) hFc hGc
    (fun w hw => by
      rw [Complex.exp_add, hc, Complex.exp_sub, hGe _ (hmaps hw), hGe _ (hmaps hw₀), hFe w hw,
        hFe w₀ hw₀]
      field_simp [hh0 _ (hmaps hw₀)])
    hw₀ (by rw [hc]; ring)
  refine ⟨fun z => (G z + c) / (2 * Real.pi * Complex.I),
    (hGa.add analyticOnNhd_const).div analyticOnNhd_const fun _ _ => two_pi_I_ne_zero,
    fun w hw => ?_⟩
  simp only
  rw [← key w hw, hFdef]
  field_simp [two_pi_I_ne_zero]
end GroundTheory.Heights₂.Heights.Regular.PeriodPolydisc
