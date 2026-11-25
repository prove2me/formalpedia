-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.PhConvProj.Sand.sand
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T10:55:04.166804+00:00
-- url     : https://prove2.me/submissions/231d5a14-437e-4916-9331-482d9d27931e

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ConvolutionProjection_ConvProjOf
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ConvolutionProjection_UrepMulApply
import Theorems.Thm_PI_UnitaryGroupMassFormula_PhConvProj_Sand_urep_mul_apply
import Theorems.Thm_PI_UnitaryGroupMassFormula_PhConvProj_Sand_urep_adj

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory
open scoped InnerProductSpace
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.PhConvProj PI.UnitaryGroupMassFormula.PhConvProj.Sand
open PI.PhConvProj
namespace PI.UnitaryGroupMassFormula.PhConvProj.Sand
theorem _root_.solution : Defs.SandStep := by
  intro G _ _ _ _ _ _ μ _ _ _ ph m hph hconv K _ _ π T hπ hT a
  ext y
  refine ext_inner_left ℂ (fun x => ?_)
  let F : G → ℂ := fun k => ⟪x, π k y⟫_ℂ
  have hFc : Continuous F := continuous_const.inner (hπ.2.2.2 y)
  have hFb : ∀ k, ‖F k‖ ≤ ‖x‖ * ‖y‖ := fun k =>
    (norm_inner_le_norm x (π k y)).trans_eq (by rw [hπ.2.2.1])
  have step1 : ∀ g, ⟪x, π g (π a (T y))⟫_ℂ = ∫ h, ph h * F (g * (a * h)) ∂μ := by
    intro g
    rw [← urep_mul_apply hπ, ← inv_inv (g * a), ← urep_adj hπ, hT]
    refine integral_congr_ae (Filter.Eventually.of_forall fun h => ?_)
    simp only [F]
    rw [urep_adj hπ, inv_inv, ← urep_mul_apply hπ, mul_assoc]
  let A : G × G → ℂ := fun z => ph z.1 * ph z.2 * F (z.1 * (a * z.2))
  have hA : Integrable A (μ.prod μ) := by
    have h1 : Integrable (fun z : G × G => ph z.1 * ph z.2) (μ.prod μ) := hph.mul_prod hph
    have hm : AEStronglyMeasurable (fun z : G × G => F (z.1 * (a * z.2))) (μ.prod μ) :=
      (hFc.comp (continuous_fst.mul (continuous_const.mul continuous_snd))).aestronglyMeasurable
    exact h1.mul_bdd hm (Filter.Eventually.of_forall fun z => hFb _)
  have e1 : ∫ g, ph g * ∫ h, ph h * F (g * (a * h)) ∂μ ∂μ = ∫ z, A z ∂(μ.prod μ) := by
    rw [integral_prod _ hA]
    refine integral_congr_ae (Filter.Eventually.of_forall fun g => ?_)
    simp only [A]
    rw [← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun h => ?_)
    simp only
    ring
  let Ψ : G × G → G × G := fun z => (z.1, z.1 * (a * z.2))
  have hΨ : MeasurePreserving Ψ (μ.prod μ) (μ.prod μ) :=
    (measurePreserving_prod_mul μ μ).comp ((MeasurePreserving.id μ).prod (measurePreserving_mul_left μ a))
  have hΨe : MeasurableEmbedding Ψ :=
    ((MeasurableEquiv.prodCongr (MeasurableEquiv.refl G) (MeasurableEquiv.mulLeft a)).trans
      (MeasurableEquiv.shearMulRight G)).measurableEmbedding
  let B : G × G → ℂ := fun z => ph z.1 * ph (a⁻¹ * z.1⁻¹ * z.2) * F z.2
  have hBA : B ∘ Ψ = A := by
    funext z
    simp only [B, Ψ, A, Function.comp]
    have : a⁻¹ * z.1⁻¹ * (z.1 * (a * z.2)) = z.2 := by group
    rw [this]
  have hB : Integrable B (μ.prod μ) := (hΨ.integrable_comp_emb hΨe).1 (hBA ▸ hA)
  have e2 : ∫ z, A z ∂(μ.prod μ) = ∫ z, B z ∂(μ.prod μ) := by
    rw [← hBA]
    exact hΨ.integral_comp hΨe B
  show ⟪x, T (π a (T y))⟫_ℂ = ⟪x, (m a • T) y⟫_ℂ
  rw [ContinuousLinearMap.smul_apply, inner_smul_right, hT x (π a (T y)), hT x y]
  simp_rw [step1]
  rw [e1, e2, integral_prod_symm B hB, ← integral_const_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun h => ?_)
  simp only [B, F]
  rw [integral_mul_const, (hconv.2.2 a h).2]
  ring
end PI.UnitaryGroupMassFormula.PhConvProj.Sand
