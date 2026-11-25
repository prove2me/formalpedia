-- Prove2me | solution 1 for QnRdSkewW.skew_reduction_analytic
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T12:35:46.325498+00:00
-- url     : https://prove2.me/submissions/e4c3c4c1-9e15-4785-b326-3cfd61711177

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SkewAnalyticGroup_IntegrableOfContOn
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SkewAnalyticGroup_Analytic
import Theorems.Thm_QnRdSkewW_ae_mem
import Theorems.Thm_QnRdSkewW_aesm_of_contOn
import Theorems.Thm_QnRdSkewW_contOn_of_smooth
import Theorems.Thm_QnRdSkewW_contOn_rdV
import Theorems.Thm_QnRdSkewW_cont_of
import Theorems.Thm_QnRdSkewW_exp_flow_cont
import Theorems.Thm_QnRdSkewW_flow_zero
import Theorems.Thm_QnRdSkewW_hasDerivAt_shift
import Theorems.Thm_QnRdSkewW_integrable_of_contOn
import Theorems.Thm_QnRdSkewW_rdV_local

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open Matrix MeasureTheory Filter Topology Set
open scoped ContDiff ENNReal
noncomputable section
namespace QnRdSkewW
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
private theorem RdV_eq_zero_of_not_mem_compact {n : ℕ} {G : Set (Matrix (Fin n) (Fin n) ℂ)}
    {X : Matrix (Fin n) (Fin n) ℂ}
    (hG : ∀ g ∈ G, ∀ t : ℝ, g * NormedSpace.exp ((t : ℂ) • X) ∈ G)
    {f : Matrix (Fin n) (Fin n) ℂ → ℂ} {K : Set (Matrix (Fin n) (Fin n) ℂ)} (hK : IsCompact K)
    (hz : ∀ g ∈ G, g ∉ K → f g = 0) {g : Matrix (Fin n) (Fin n) ℂ} (hg : g ∈ G) (hgK : g ∉ K) :
    RdV X f g = 0 := by
  rw [rdV_local (F := fun _ => (0 : ℂ)) hG hK.isClosed.isOpen_compl hgK contDiffOn_const
    (fun h hU hGh => hz h hGh hU) hg]
  simp
end QnRdSkewW
end
end

set_option autoImplicit false
open Matrix MeasureTheory Filter Topology Set
open scoped ContDiff ENNReal
noncomputable section
open QnRdSkewW
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
namespace QnRdSkewW
theorem _root_.solution : StepAnalytic := by
  intro n G μ X f₁ f₂ hGc hG hconc hinv hfin hs₁ hs₂ hK₁ _
  obtain ⟨K₁, hK₁c, hz₁⟩ := hK₁
  have hc₁ := contOn_of_smooth hs₁
  have hc₂ := contOn_of_smooth hs₂
  have hd₁ : ContinuousOn (RdV X f₁) G := contOn_rdV hG hs₁
  have hd₂ : ContinuousOn (RdV X f₂) G := contOn_rdV hG hs₂
  have hr₁ : ∀ g ∈ G, g ∉ K₁ → RdV X f₁ g = 0 := fun g hg hgK => RdV_eq_zero_of_not_mem_compact hG hK₁c hz₁ hg hgK
  have hPc : ContinuousOn (fun g => f₁ g * star (f₂ g)) G := hc₁.mul hc₂.star
  have hQc : ContinuousOn (fun g => RdV X f₁ g * star (f₂ g) + f₁ g * star (RdV X f₂ g)) G :=
    (hd₁.mul hc₂.star).add (hc₁.mul hd₂.star)
  have hQz : ∀ g ∈ G, g ∉ K₁ → RdV X f₁ g * star (f₂ g) + f₁ g * star (RdV X f₂ g) = 0 := by
    intro g hg hgK
    rw [hr₁ g hg hgK, hz₁ g hg hgK]
    simp
  have hrm : ∀ a : Matrix (Fin n) (Fin n) ℂ, Measurable (B.rmulF a) := fun a =>
    Continuous.measurable (show Continuous (B.rmulF a) from cont_of.matrix_mul continuous_const)
  have hinvI : ∀ t : ℝ,
      ∫ x, f₁ (Matrix.of x * NormedSpace.exp ((t : ℂ) • X)) *
          star (f₂ (Matrix.of x * NormedSpace.exp ((t : ℂ) • X))) ∂μ =
        ∫ x, f₁ (Matrix.of x) * star (f₂ (Matrix.of x)) ∂μ := by
    intro t
    have hsm : AEStronglyMeasurable (fun y : Fin n → Fin n → ℂ => f₁ (Matrix.of y) * star (f₂ (Matrix.of y)))
        (μ.map (B.rmulF (NormedSpace.exp ((t : ℂ) • X)))) := by
      rw [hinv t]
      exact aesm_of_contOn hGc hconc hPc
    have h := integral_map (hrm (NormedSpace.exp ((t : ℂ) • X))).aemeasurable hsm
    rw [hinv t] at h
    exact h.symm
  have hF_meas : ∀ᶠ t : ℝ in 𝓝 (0 : ℝ), AEStronglyMeasurable (fun x : Fin n → Fin n → ℂ =>
      f₁ (Matrix.of x * NormedSpace.exp ((t : ℂ) • X)) *
        star (f₂ (Matrix.of x * NormedSpace.exp ((t : ℂ) • X)))) μ :=
    Filter.Eventually.of_forall fun t =>
      aesm_of_contOn (φ := fun g => f₁ (g * NormedSpace.exp ((t : ℂ) • X)) *
          star (f₂ (g * NormedSpace.exp ((t : ℂ) • X)))) hGc hconc
        (hPc.comp (continuous_id.matrix_mul continuous_const).continuousOn fun g hg => hG g hg t)
  have hF_int : Integrable (fun x : Fin n → Fin n → ℂ =>
      f₁ (Matrix.of x * NormedSpace.exp (((0 : ℝ) : ℂ) • X)) *
        star (f₂ (Matrix.of x * NormedSpace.exp (((0 : ℝ) : ℂ) • X)))) μ := by
    simp only [flow_zero]
    exact integrable_of_contOn hGc hconc hfin hPc hK₁c (fun g hg hgK => by simp [hz₁ g hg hgK])
  have hF'_meas : AEStronglyMeasurable (fun x : Fin n → Fin n → ℂ =>
      RdV X f₁ (Matrix.of x * NormedSpace.exp (((0 : ℝ) : ℂ) • X)) *
          star (f₂ (Matrix.of x * NormedSpace.exp (((0 : ℝ) : ℂ) • X))) +
        f₁ (Matrix.of x * NormedSpace.exp (((0 : ℝ) : ℂ) • X)) *
          star (RdV X f₂ (Matrix.of x * NormedSpace.exp (((0 : ℝ) : ℂ) • X)))) μ := by
    simp only [flow_zero]
    exact aesm_of_contOn hGc hconc hQc
  obtain ⟨C, hC⟩ := (hK₁c.inter_left hGc).exists_bound_of_continuousOn (hQc.mono Set.inter_subset_left)
  set L : Set (Matrix (Fin n) (Fin n) ℂ) :=
    (fun p : Matrix (Fin n) (Fin n) ℂ × ℝ => p.1 * NormedSpace.exp ((p.2 : ℂ) • X)) ''
      (K₁ ×ˢ Icc (-1 : ℝ) 1) with hLdef
  have hL : IsCompact L :=
    (hK₁c.prod isCompact_Icc).image (continuous_fst.matrix_mul ((exp_flow_cont X).comp continuous_snd))
  have hS : IsCompact (Matrix.of ⁻¹' L : Set (Fin n → Fin n → ℂ)) := hL
  have hbound_int : Integrable ((Matrix.of ⁻¹' L).indicator fun _ => max C 0) μ :=
    (integrable_indicator_iff hS.measurableSet).2 (integrableOn_const (hfin _ hS).ne)
  have h_bound : ∀ᵐ x ∂μ, ∀ t ∈ Metric.ball (0 : ℝ) 1,
      ‖RdV X f₁ (Matrix.of x * NormedSpace.exp ((t : ℂ) • X)) *
            star (f₂ (Matrix.of x * NormedSpace.exp ((t : ℂ) • X))) +
          f₁ (Matrix.of x * NormedSpace.exp ((t : ℂ) • X)) *
            star (RdV X f₂ (Matrix.of x * NormedSpace.exp ((t : ℂ) • X)))‖ ≤
        (Matrix.of ⁻¹' L).indicator (fun _ => max C 0) x := by
    filter_upwards [ae_mem hconc] with x hx t ht
    have hgt := hG _ hx t
    by_cases hk : Matrix.of x * NormedSpace.exp ((t : ℂ) • X) ∈ K₁
    · have ht' : |t| < 1 := by simpa [Real.dist_eq] using ht
      have hxS : x ∈ (Matrix.of ⁻¹' L : Set (Fin n → Fin n → ℂ)) := by
        refine ⟨(Matrix.of x * NormedSpace.exp ((t : ℂ) • X), -t),
          ⟨hk, by linarith [abs_lt.1 ht'], by linarith [abs_lt.1 ht']⟩, ?_⟩
        have hcomm : Commute ((t : ℂ) • X) (-((t : ℂ) • X)) := (Commute.refl _).neg_right
        show Matrix.of x * NormedSpace.exp ((t : ℂ) • X) * NormedSpace.exp (((-t : ℝ) : ℂ) • X) =
          Matrix.of x
        rw [mul_assoc, show (((-t : ℝ) : ℂ) • X) = -((t : ℂ) • X) by push_cast; exact neg_smul _ _,
          ← Matrix.exp_add_of_commute _ _ hcomm, add_neg_cancel, NormedSpace.exp_zero, mul_one]
      rw [Set.indicator_of_mem hxS]
      exact (hC _ ⟨hgt, hk⟩).trans (le_max_left _ _)
    · rw [hQz _ hgt hk, norm_zero]
      exact Set.indicator_nonneg (fun _ _ => le_max_right _ _) _
  have h_diff : ∀ᵐ x ∂μ, ∀ t ∈ Metric.ball (0 : ℝ) 1,
      HasDerivAt (fun s : ℝ => f₁ (Matrix.of x * NormedSpace.exp ((s : ℂ) • X)) *
          star (f₂ (Matrix.of x * NormedSpace.exp ((s : ℂ) • X))))
        (RdV X f₁ (Matrix.of x * NormedSpace.exp ((t : ℂ) • X)) *
            star (f₂ (Matrix.of x * NormedSpace.exp ((t : ℂ) • X))) +
          f₁ (Matrix.of x * NormedSpace.exp ((t : ℂ) • X)) *
            star (RdV X f₂ (Matrix.of x * NormedSpace.exp ((t : ℂ) • X)))) t := by
    filter_upwards [ae_mem hconc] with x hx t _
    exact (hasDerivAt_shift hG hs₁ hx t).mul (hasDerivAt_shift hG hs₂ hx t).star
  have hderiv := (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := fun (t : ℝ) (x : Fin n → Fin n → ℂ) => f₁ (Matrix.of x * NormedSpace.exp ((t : ℂ) • X)) *
      star (f₂ (Matrix.of x * NormedSpace.exp ((t : ℂ) • X))))
    (F' := fun (t : ℝ) (x : Fin n → Fin n → ℂ) =>
      RdV X f₁ (Matrix.of x * NormedSpace.exp ((t : ℂ) • X)) *
          star (f₂ (Matrix.of x * NormedSpace.exp ((t : ℂ) • X))) +
        f₁ (Matrix.of x * NormedSpace.exp ((t : ℂ) • X)) *
          star (RdV X f₂ (Matrix.of x * NormedSpace.exp ((t : ℂ) • X))))
    (Metric.ball_mem_nhds (0 : ℝ) one_pos) hF_meas hF_int hF'_meas h_bound hbound_int h_diff).2
  have hconst : HasDerivAt (fun _ : ℝ => ∫ x, f₁ (Matrix.of x) * star (f₂ (Matrix.of x)) ∂μ)
      (∫ x, (RdV X f₁ (Matrix.of x * NormedSpace.exp (((0 : ℝ) : ℂ) • X)) *
          star (f₂ (Matrix.of x * NormedSpace.exp (((0 : ℝ) : ℂ) • X))) +
        f₁ (Matrix.of x * NormedSpace.exp (((0 : ℝ) : ℂ) • X)) *
          star (RdV X f₂ (Matrix.of x * NormedSpace.exp (((0 : ℝ) : ℂ) • X)))) ∂μ) 0 := by
    exact hderiv.congr_of_eventuallyEq (Filter.Eventually.of_forall fun t => (hinvI t).symm)
  have h0 := hconst.unique (hasDerivAt_const _ _)
  simp only [flow_zero] at h0
  have hI1 : Integrable (fun x : Fin n → Fin n → ℂ => RdV X f₁ (Matrix.of x) * star (f₂ (Matrix.of x))) μ :=
    integrable_of_contOn hGc hconc hfin (hd₁.mul hc₂.star) hK₁c (fun g hg hgK => by simp [hr₁ g hg hgK])
  have hI2 : Integrable (fun x : Fin n → Fin n → ℂ => f₁ (Matrix.of x) * star (RdV X f₂ (Matrix.of x))) μ :=
    integrable_of_contOn hGc hconc hfin (hc₁.mul hd₂.star) hK₁c (fun g hg hgK => by simp [hz₁ g hg hgK])
  rw [integral_add hI1 hI2] at h0
  exact eq_neg_of_add_eq_zero_left h0
end QnRdSkewW
