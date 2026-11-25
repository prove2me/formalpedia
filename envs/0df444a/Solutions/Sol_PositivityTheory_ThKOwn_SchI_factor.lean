-- Prove2me | solution 1 for PositivityTheory.ThKOwn.SchI.factor
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T12:02:44.320392+00:00
-- url     : https://prove2.me/submissions/894419c4-8568-47c7-910d-16a665df2389

import Mathlib
import Definitions.Def_Development_WeilBound_ThetaLifts_SchwartzMoments_JetApply
import Theorems.Thm_PositivityTheory_ThKOwn_SchI_J_apply

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PositivityTheory PositivityTheory.ThKOwn
open PositivityTheory.ThKOwn.SchI
open scoped ContDiff NNReal BoundedContinuousFunction
open MeasureTheory Filter Topology
variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
variable {α : Type} [TopologicalSpace α] [SecondCountableTopology α] [MeasurableSpace α] [BorelSpace α] {μ : Measure α}
  {G : α → SchwartzMap V ℂ} (hG : Continuous G) (hI : ∀ k j : ℕ, Integrable (fun a => SchwartzMap.seminorm ℂ k j (G a)) μ)
include hG hI
omit hG hI
namespace PositivityTheory.ThKOwn.SchI
theorem _root_.solution (T : SchwartzMap V ℂ →L[ℂ] ℂ) : ∃ (s : Finset (ℕ × ℕ))
    (T' : (∀ i : s, V →ᵇ (V [×i.1.2]→L[ℝ] ℂ)) →L[ℂ] ℂ), ∀ f, T f = T' fun i => J i.1.1 i.1.2 f := by
  obtain ⟨s, C, -, hC⟩ := Seminorm.bound_of_continuous (schwartz_withSeminorms ℂ V ℂ)
    ((normSeminorm ℂ ℂ).comp T.toLinearMap) (continuous_norm.comp T.continuous)
  let Φ : SchwartzMap V ℂ →ₗ[ℂ] (∀ i : s, V →ᵇ (V [×i.1.2]→L[ℝ] ℂ)) :=
    LinearMap.pi fun i => (J i.1.1 i.1.2 : SchwartzMap V ℂ →L[ℂ] _).toLinearMap
  have hbound : ∀ f, ‖T f‖ ≤ C * ‖Φ f‖ := by
    intro f
    have h1 : ‖T f‖ ≤ (C : ℝ) * (s.sup (schwartzSeminormFamily ℂ V ℂ)) f := hC f
    refine h1.trans (mul_le_mul_of_nonneg_left ?_ C.2)
    refine Seminorm.finset_sup_apply_le (norm_nonneg _) fun i hi => ?_
    have h2 : ‖J i.1 i.2 f‖ ≤ ‖Φ f‖ := norm_le_pi_norm (Φ f) ⟨i, hi⟩
    rw [J_apply, norm_jet] at h2
    exact h2
  have hker : LinearMap.ker Φ ≤ LinearMap.ker T.toLinearMap := by
    intro f hf
    rw [LinearMap.mem_ker] at hf ⊢
    have h := hbound f
    rw [hf, norm_zero, mul_zero] at h
    exact norm_le_zero_iff.1 h
  let g₀ : LinearMap.range Φ →ₗ[ℂ] ℂ :=
    (LinearMap.ker Φ).liftQ T.toLinearMap hker ∘ₗ Φ.quotKerEquivRange.symm.toLinearMap
  have hg₀ : ∀ f, g₀ ⟨Φ f, LinearMap.mem_range_self Φ f⟩ = T f := by
    intro f
    simp only [g₀, LinearMap.comp_apply, LinearEquiv.coe_coe]
    rw [LinearMap.quotKerEquivRange_symm_apply_image]
    rfl
  have hg₀b : ∀ v, ‖g₀ v‖ ≤ C * ‖v‖ := by
    rintro ⟨_, f, rfl⟩
    show ‖g₀ ⟨Φ f, LinearMap.mem_range_self Φ f⟩‖ ≤ C * ‖Φ f‖
    rw [hg₀]
    exact hbound f
  obtain ⟨T', hT', -⟩ := exists_extension_norm_eq (LinearMap.range Φ) (g₀.mkContinuous C hg₀b)
  refine ⟨s, T', fun f => ?_⟩
  have h := hT' ⟨Φ f, LinearMap.mem_range_self Φ f⟩
  rw [LinearMap.mkContinuous_apply, hg₀] at h
  exact h.symm
end PositivityTheory.ThKOwn.SchI
