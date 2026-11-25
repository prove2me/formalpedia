-- Prove2me | solution 1 for PositivityTheory.ThKF.L2.integral_deriv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T12:05:43.481186+00:00
-- url     : https://prove2.me/submissions/46c57c79-8e1f-434f-92fc-41cdfd4e78a6

import Mathlib
import Definitions.Def_Development_WeilBound_ThetaLifts_CartanFactorisation_IntegrableOnRight
import Theorems.Thm_PositivityTheory_ThKF_L2_integral_right
import Theorems.Thm_PositivityTheory_ThKF_L2_integrableOn_right

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PositivityTheory PositivityTheory.ThKF PositivityTheory.ThKF.L2
open MeasureTheory
open scoped ComplexConjugate Pointwise
variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G] [BorelSpace G]
  {μ : Measure G} [μ.IsHaarMeasure] [μ.IsMulRightInvariant] {Γ : Subgroup G} [Countable Γ] {𝓕 : Set G}
namespace PositivityTheory.ThKF.L2
theorem _root_.solution [SFinite μ] (h : IsFundamentalDomain Γ 𝓕 μ) (γ : Multiplicative ℝ →* G) (hγ : Continuous γ)
    {F F₁ : G → ℂ} (c₁ : Continuous F₁) (hF : Inv Γ F) (hF₁ : Inv Γ F₁) (iF : IntegrableOn F 𝓕 μ)
    (iF₁ : IntegrableOn F₁ 𝓕 μ) (hd : ∀ x, HasDerivAt (fun t : ℝ => F (x * γ (Multiplicative.ofAdd t))) (F₁ x) 0) :
    ∫ x in 𝓕, F₁ x ∂μ = 0 := by
  have cg : Continuous fun t : ℝ => γ (Multiplicative.ofAdd t) := hγ.comp continuous_ofAdd
  have hd' : ∀ x s, HasDerivAt (fun t : ℝ => F (x * γ (Multiplicative.ofAdd t))) (F₁ (x * γ (Multiplicative.ofAdd s))) s := by
    intro x s
    have h1 := hd (x * γ (Multiplicative.ofAdd s))
    have h2 : HasDerivAt (fun t : ℝ => t - s) 1 s := (hasDerivAt_id s).sub_const s
    have h3 := HasDerivAt.scomp s (by simpa using h1) h2
    simp only [one_smul] at h3
    refine h3.congr_of_eventuallyEq (Filter.Eventually.of_forall fun t => ?_)
    show F _ = F (x * γ (Multiplicative.ofAdd s) * γ (Multiplicative.ofAdd (t - s)))
    rw [mul_assoc, ← map_mul, ← ofAdd_add, add_sub_cancel]
  have ftc : ∀ x, ∫ s in (0 : ℝ)..1, F₁ (x * γ (Multiplicative.ofAdd s)) = F (x * γ (Multiplicative.ofAdd 1)) - F x := by
    intro x
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun s _ => hd' x s)
      ((c₁.comp (continuous_const.mul cg)).intervalIntegrable _ _)]
    simp
  have cj : Continuous fun p : ℝ × G => F₁ (p.2 * γ (Multiplicative.ofAdd p.1)) :=
    c₁.comp (continuous_snd.mul (cg.comp continuous_fst))
  have ij : Integrable (Function.uncurry fun (s : ℝ) (x : G) => F₁ (x * γ (Multiplicative.ofAdd s)))
      ((volume.restrict (Set.Ioc (0 : ℝ) 1)).prod (μ.restrict 𝓕)) := by
    refine (integrable_prod_iff cj.aestronglyMeasurable).2 ⟨Filter.Eventually.of_forall fun s =>
      integrableOn_right h F₁ hF₁ iF₁ (γ (Multiplicative.ofAdd s)), ?_⟩
    have : (fun s : ℝ => ∫ x in 𝓕, ‖F₁ (x * γ (Multiplicative.ofAdd s))‖ ∂μ) = fun _ => ∫ x in 𝓕, ‖F₁ x‖ ∂μ :=
      funext fun s => integral_right h (fun x => ‖F₁ x‖) (fun g hg x => by rw [hF₁ g hg]) _
    simp only
    rw [this]
    exact integrable_const _
  have sw := integral_integral_swap ij
  have l : ∫ s in Set.Ioc (0 : ℝ) 1, ∫ x in 𝓕, F₁ (x * γ (Multiplicative.ofAdd s)) ∂μ = ∫ x in 𝓕, F₁ x ∂μ := by
    simp [integral_right h F₁ hF₁]
  have r : ∫ x in 𝓕, (∫ s in Set.Ioc (0 : ℝ) 1, F₁ (x * γ (Multiplicative.ofAdd s))) ∂μ = 0 := by
    simp only [← intervalIntegral.integral_of_le zero_le_one, ftc]
    rw [integral_sub (integrableOn_right h F hF iF _) iF, integral_right h F hF, sub_self]
  rw [← l, sw, r]
end PositivityTheory.ThKF.L2
