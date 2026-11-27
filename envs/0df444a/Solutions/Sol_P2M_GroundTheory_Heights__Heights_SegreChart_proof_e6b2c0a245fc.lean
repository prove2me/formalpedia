-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_SegreChart_proof_e6b2c0a245fc
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-27T05:09:12.544715+00:00
-- url     : https://prove2.me/submissions/047cd4f9-adf9-4cc5-ae1a-9fc4613ec61e

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StSegreChart
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StSegreChartDim
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StSegreChartIntegral
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_PSegreChart
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_pot_cons_expLine_9bc1a22b6dbc
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_isSmoothHerm_cons_expLine_97c9cbe268f7
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IsDegZeroSmooth_mul_ac2f2d59f4e1
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_chartLift_blockNonzero_4a49d0f77c5b
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_chart_coord_eq_one_2829753f3694
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_contDiff_chartLift_8692f480c9b0
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_mem_segreChartComponents_1a9d50ef3666
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_segre_chartLift_cde5bc6f2110
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_isOpen_blockNonzero


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open Filter Topology
open scoped ContDiff
open ReciprocityTheory.ChartRestriction.G.Geo (MRing HermLine IsSmoothHerm IsArithVar ptsIntegral pot segre isOpen_blockNonzero)
namespace GroundTheory.Heights₂.Heights
namespace SegreChart
theorem _root_.solution (hDim : SegreChartDim.Statement) (hInt : SegreChartIntegral.Statement) :
    SegreChart.Statement := by
  classical
  intro K _ _ ι _ P n L u v i δ hP hL hu hv hδ hsupp
  let σ := (Fintype.equivFin ((k : K) → ι k)).symm
  let lam := chartLift σ i
  let χ : ContDiffBump (0 : Fin (Fintype.card ((k : K) → ι k)) → ℂ) :=
    ⟨1 / δ + 1, 1 / δ + 2, by positivity, by linarith⟩
  let U := fun x => χ x * u (lam x)
  let V := fun x => v (lam x)
  let Φ : Fin n → _ := fun j x => pot L j (lam x)
  have hlam : ContDiff ℝ ∞ lam := contDiff_chartLift σ i

  let Ω := lam ⁻¹' {z | ∀ k, ∃ j, z ⟨k, j⟩ ≠ 0}
  have hΩ : IsOpen Ω := isOpen_blockNonzero.preimage hlam.continuous
  have hsm : ∀ f : ((Σ k, ι k) → ℂ) → ℝ, ContDiffOn ℝ ∞ f {z | ∀ k, ∃ j, z ⟨k, j⟩ ≠ 0} →
      ContDiffOn ℝ ∞ (f ∘ lam) Ω := fun f hf => hf.comp hlam.contDiffOn fun _ hx => hx
  have hpot : ∀ j, ContDiffOn ℝ ∞ (pot L j) {z | ∀ k, ∃ j, z ⟨k, j⟩ ≠ 0} := fun j =>
    (hL j).log fun z hz => ((L j).pos z hz).ne'

  have key : ∀ x ∈ segreChartSet P σ i, U =ᶠ[𝓝 x] u ∘ lam := by
    rintro _ ⟨z, -, hzi, rfl⟩
    by_cases hr : ‖fun a => segre z (σ a)‖ < 1 / δ + 1
    · filter_upwards [Metric.isOpen_ball.mem_nhds (mem_ball_zero_iff.2 hr)] with y hy
      simp [U, χ.one_of_mem_closedBall (Metric.ball_subset_closedBall hy)]
    · have hle : ‖fun a => segre z (σ a)‖ ≤ ‖segre z‖ :=
        (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun a => norm_le_pi_norm (segre z) (σ a)
      have hcont : Continuous fun y => segre (lam y) :=
        continuous_pi fun i' => continuous_finsetProd _ fun k _ =>
          (continuous_apply (⟨k, i' k⟩ : Σ k, ι k)).comp hlam.continuous
      have hO : IsOpen {y | ‖segre (lam y) i‖ < δ * ‖segre (lam y)‖} :=
        isOpen_lt ((continuous_apply i).comp hcont).norm (continuous_const.mul hcont.norm)
      have hx : ‖segre (lam fun a => segre z (σ a)) i‖ < δ * ‖segre (lam fun a => segre z (σ a))‖ := by
        rw [segre_chartLift σ i z hzi, hzi, norm_one]
        have h1 : 1 / δ < ‖segre z‖ := by linarith
        calc (1 : ℝ) = δ * (1 / δ) := by field_simp
          _ < δ * ‖segre z‖ := mul_lt_mul_of_pos_left h1 hδ
      filter_upwards [hO.mem_nhds hx] with y hy
      simp [U, hsupp _ hy]
  have hJ : ∀ J ∈ segreChartComponents P σ i, ComplexSets.zeroSet J ⊆ Ω := fun J hJ x hx =>
    chartLift_blockNonzero σ i (chart_coord_eq_one hJ hx)
  refine ⟨Fintype.card ((k : K) → ι k), segreChartComponents P σ i, U, V, Φ,
    fun J hJs => ⟨(mem_segreChartComponents.1 hJs).1.1,
      hDim K ι P (n + 1) _ σ i hP J hJs,
      ⟨Ω, hΩ, hJ J hJs, (χ.contDiff.contDiffOn).mul (hsm u hu.1)⟩,
      ⟨Ω, hΩ, hJ J hJs, hsm v hv.1⟩, fun j => ⟨Ω, hΩ, hJ J hJs, hsm _ (hpot j)⟩⟩,
    χ.hasCompactSupport.mul_right, ?_, ?_⟩
  · rw [← pot_cons_expLine v hv L]
    refine hInt K ι P n _ σ i _ u δ U _ hP (isSmoothHerm_cons_expLine v hv L hL) hu hδ (Or.inl hsupp)
      fun x hx => ⟨key x hx, fun j => EventuallyEq.of_eq ?_⟩
    refine Fin.cases ?_ (fun j => ?_) j
    · funext y; simp [V, lam, pot, expLine, HermLine.ofWeight]
    · rfl
  · rw [← pot_cons_expLine u hu L]
    refine hInt K ι P n _ σ i _ v δ V _ hP (isSmoothHerm_cons_expLine u hu L hL) hv hδ
      (Or.inr fun z hz => by rw [pot_cons_expLine u hu L]; exact hsupp z hz)
      fun x hx => ⟨EventuallyEq.rfl, fun j => ?_⟩
    refine Fin.cases ?_ (fun j => ?_) j
    · have h0 : pot (Fin.cons (expLine u hu) L : Fin (n + 1) → HermLine ι) 0 = u := by
        rw [pot_cons_expLine u hu L]; rfl
      simpa [h0] using key x hx
    · exact EventuallyEq.rfl
end SegreChart
end GroundTheory.Heights₂.Heights
