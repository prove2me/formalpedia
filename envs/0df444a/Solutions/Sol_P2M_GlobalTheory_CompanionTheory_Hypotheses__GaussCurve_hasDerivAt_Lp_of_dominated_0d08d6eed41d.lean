-- Prove2me | solution 1 for P2M_GlobalTheory_CompanionTheory_Hypotheses__GaussCurve_hasDerivAt_Lp_of_dominated_0d08d6eed41d
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-27T04:50:49.396267+00:00
-- url     : https://prove2.me/submissions/9dccb892-c1aa-4181-bc3d-4c04962cee60

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_TwistedTraceFormula_RealMetaplecticRepresentation
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_TwistedTraceFormula_MetaplecticRepresentation
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_TwistedTraceFormula_HolPartShear
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IteratedLineDerivMemWeylAlg
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_RealMpData
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MembershipProofs_NormIteratedFDerivCexpCompLe
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_HasDerivAtLpOfDominated
import Theorems.Thm_P2M_GlobalTheory_CompanionTheory_Hypotheses__GaussCurve_lp_two_norm_sq_05878a2e21aa

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Complex Matrix GlobalTheory.RealWeil GlobalTheory.CompanionTheory.Hypotheses₂ Filter Topology
open scoped Real SchwartzMap ComplexConjugate
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Hypotheses₂ GlobalTheory.CompanionTheory.Hypotheses₂.GaussCurve
namespace GlobalTheory.CompanionTheory.Hypotheses₂.GaussCurve
theorem _root_.solution {E : Type*} [MeasurableSpace E] {μ : Measure E}
    (F : ℝ → Lp ℂ 2 μ) (G : Lp ℂ 2 μ) (f f' : ℝ → E → ℂ) (b : E → ℝ) (t₀ δ : ℝ) (hδ : 0 < δ)
    (hF : ∀ t, F t =ᵐ[μ] f t) (hG : G =ᵐ[μ] f' t₀) (hb : MemLp b 2 μ)
    (hd : ∀ x, ∀ t ∈ Metric.ball t₀ δ, HasDerivAt (fun s => f s x) (f' t x) t)
    (hbd : ∀ x, ∀ t ∈ Metric.ball t₀ δ, ‖f' t x‖ ≤ b x) :
    HasDerivAt F G t₀ := by
  rw [hasDerivAt_iff_tendsto_slope_zero]
  set d : ℝ → E → ℂ := fun s x => (s⁻¹ : ℝ) • (f (t₀ + s) x - f t₀ x) - f' t₀ x with hd_def
  have hD : ∀ s : ℝ, ((s⁻¹ • (F (t₀ + s) - F t₀) - G : Lp ℂ 2 μ) : E → ℂ) =ᵐ[μ] d s := by
    intro s
    filter_upwards [Lp.coeFn_sub (s⁻¹ • (F (t₀ + s) - F t₀)) G,
      Lp.coeFn_smul s⁻¹ (F (t₀ + s) - F t₀), Lp.coeFn_sub (F (t₀ + s)) (F t₀),
      hF (t₀ + s), hF t₀, hG] with x h1 h2 h3 h4 h5 h6
    simp only [hd_def, h1, Pi.sub_apply, h2, Pi.smul_apply, h3, h4, h5, h6]
  have hsq : ∀ s : ℝ, ‖s⁻¹ • (F (t₀ + s) - F t₀) - G‖ ^ 2 = ∫ x, ‖d s x‖ ^ 2 ∂μ := by
    intro s
    rw [lp_two_norm_sq]
    exact integral_congr_ae ((hD s).mono fun x hx => by simp only [hx])
  have hlim : Tendsto (fun s : ℝ => ∫ x, ‖d s x‖ ^ 2 ∂μ) (𝓝[≠] 0) (𝓝 (∫ _x, (0 : ℝ) ∂μ)) := by
    refine tendsto_integral_filter_of_dominated_convergence (fun x => (2 * b x) ^ 2) ?_ ?_ ?_ ?_
    · exact Eventually.of_forall fun s =>
        (((Lp.aestronglyMeasurable _).congr (hD s)).norm.pow 2)
    · have hs : ∀ᶠ s : ℝ in 𝓝[≠] 0, s ≠ 0 ∧ |s| < δ := by
        have h1 : ∀ᶠ s : ℝ in 𝓝[≠] 0, s ≠ 0 := eventually_mem_nhdsWithin
        have h2 : ∀ᶠ s : ℝ in 𝓝[≠] 0, |s| < δ := by
          refine nhdsWithin_le_nhds ?_
          have : ∀ᶠ s : ℝ in 𝓝 0, s ∈ Metric.ball (0 : ℝ) δ := Metric.ball_mem_nhds _ hδ
          exact this.mono fun s hs => by simpa using hs
        exact h1.and h2
      refine hs.mono fun s hs => Eventually.of_forall fun x => ?_
      obtain ⟨hs0, hsδ⟩ := hs
      have hmem : t₀ + s ∈ Metric.ball t₀ δ := by simpa [Metric.mem_ball, dist_eq_norm] using hsδ
      have h0 : t₀ ∈ Metric.ball t₀ δ := Metric.mem_ball_self hδ
      have hmv : ‖f (t₀ + s) x - f t₀ x‖ ≤ b x * ‖(t₀ + s) - t₀‖ :=
        (convex_ball t₀ δ).norm_image_sub_le_of_norm_hasDerivWithin_le
          (f := fun r => f r x) (f' := fun r => f' r x)
          (fun r hr => (hd x r hr).hasDerivWithinAt) (fun r hr => hbd x r hr) h0 hmem
      have hb0 : 0 ≤ b x := (norm_nonneg _).trans (hbd x t₀ h0)
      have hq : ‖(s⁻¹ : ℝ) • (f (t₀ + s) x - f t₀ x)‖ ≤ b x := by
        rw [norm_smul, norm_inv]
        have hn : 0 < ‖s‖ := norm_pos_iff.2 hs0
        rw [add_sub_cancel_left] at hmv
        rw [inv_mul_le_iff₀ hn]
        linarith [mul_comm (b x) ‖s‖]
      have hdn : ‖d s x‖ ≤ 2 * b x := by
        calc ‖d s x‖ ≤ ‖(s⁻¹ : ℝ) • (f (t₀ + s) x - f t₀ x)‖ + ‖f' t₀ x‖ := norm_sub_le _ _
          _ ≤ 2 * b x := by linarith [hbd x t₀ h0]
      rw [Real.norm_of_nonneg (by positivity)]
      exact pow_le_pow_left₀ (norm_nonneg _) hdn 2
    · have := (memLp_two_iff_integrable_sq hb.1).1 hb
      simpa [mul_pow] using this.const_mul (2 ^ 2)
    · refine Eventually.of_forall fun x => ?_
      have h1 := hasDerivAt_iff_tendsto_slope_zero.1 (hd x t₀ (Metric.mem_ball_self hδ))
      have h2 : Tendsto (fun s : ℝ => d s x) (𝓝[≠] 0) (𝓝 (f' t₀ x - f' t₀ x)) :=
        h1.sub tendsto_const_nhds
      have h3 := (h2.norm).pow 2
      simpa using h3
  have hlim0 : Tendsto (fun s : ℝ => ‖s⁻¹ • (F (t₀ + s) - F t₀) - G‖ ^ 2) (𝓝[≠] 0) (𝓝 0) := by
    simp only [hsq]
    simpa using hlim
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have h4 := (Real.continuous_sqrt.tendsto 0).comp hlim0
  simpa [Function.comp_def, Real.sqrt_sq (norm_nonneg _)] using h4
end GlobalTheory.CompanionTheory.Hypotheses₂.GaussCurve
