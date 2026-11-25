-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.slm_gen_hD
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T12:43:25.852862+00:00
-- url     : https://prove2.me/submissions/260dabe3-6a08-40de-a983-37488769eeba

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_DiscreteSeriesExistence_CayleyChartDomainIsOpen
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_DiscreteSeriesExistence_ContDiffOnZeroOfContinuousOn
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_slmG_cd
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_contDiffOn_zero_of_continuousOn

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Set Filter Topology Matrix
open scoped ContDiff
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS
variable {X Y E : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [NormedAddCommGroup Y] [NormedSpace ℝ Y]
  [NormedAddCommGroup E] [NormedSpace ℂ E] {ι : Type*} [Fintype ι]
namespace ReciprocityTheory.ChartRestriction.DS
theorem _root_.solution {V : Set X} (hV : IsOpen V) {γ : X → Y} (hγ : ContDiffOn ℝ ∞ γ V)
    (C : ι → Y →L[ℝ] ℝ) {A : Type*} (c : ι → X → ℂ) (hc : ∀ i, ContDiffOn ℝ ∞ (c i) V)
    (P : A → Prop) (Op : ι → A → A) (hP : ∀ F, P F → ∀ i, P (Op i F)) (Φ : A → X → E)
    (hcont : ∀ F, P F → ContinuousOn (Φ F) V)
    (hint : ∀ F, P F → ∀ q ∈ V, ∃ δ > 0, ∀ W : X, ‖W‖ < δ → ∀ B : ℝ,
      (∀ s ∈ Ioc (0:ℝ) 1, ‖slmG C (fderiv ℝ γ (q + s • W))
          (fun i => c i (q + s • W) • Φ (Op i F) (q + s • W)) W -
        slmG C (fderiv ℝ γ q) (fun i => c i q • Φ (Op i F) q) W‖ ≤ B) →
      ‖Φ F (q + W) - Φ F q - slmG C (fderiv ℝ γ q) (fun i => c i q • Φ (Op i F) q) W‖ ≤ B) :
    ∀ F, P F → ∀ q ∈ V,
      HasFDerivAt (Φ F) (slmG C (fderiv ℝ γ q) (fun i => c i q • Φ (Op i F) q)) q := by
  intro F hF q hq
  set L : X → (X →L[ℝ] E) := fun x => slmG C (fderiv ℝ γ x) (fun i => c i x • Φ (Op i F) x)
    with hLdef
  have hw0 : ∀ i, ContDiffOn ℝ ((0 : ℕ) : WithTop ℕ∞) (fun x => c i x • Φ (Op i F) x) V :=
    fun i => contDiffOn_zero_of_continuousOn (((hc i).continuousOn).smul (hcont (Op i F) (hP F hF i)))
  have hLc : ContinuousAt L q :=
    ((slmG_cd hV hγ C hw0).continuousOn).continuousAt (hV.mem_nhds hq)
  rw [hasFDerivAt_iff_isLittleO_nhds_zero, Asymptotics.isLittleO_iff]
  intro ε hε
  obtain ⟨ρ, hρ, hρL⟩ := Metric.continuousAt_iff.mp hLc ε hε
  obtain ⟨δ, hδ, hδh⟩ := hint F hF q hq
  have hball : ∀ᶠ W in 𝓝 (0 : X), ‖W‖ < min δ ρ := by
    have := Metric.ball_mem_nhds (0 : X) (lt_min hδ hρ)
    filter_upwards [this] with W hW
    simpa using hW
  filter_upwards [hball] with W hW
  apply hδh W (lt_of_lt_of_le hW (min_le_left _ _)) (ε * ‖W‖)
  intro s hs
  have hd : dist (q + s • W) q < ρ := by
    rw [dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_pos hs.1]
    calc s * ‖W‖ ≤ 1 * ‖W‖ := mul_le_mul_of_nonneg_right hs.2 (norm_nonneg _)
      _ = ‖W‖ := one_mul _
      _ < ρ := lt_of_lt_of_le hW (min_le_right _ _)
  have h1 := hρL hd
  rw [dist_eq_norm] at h1
  calc ‖L (q + s • W) W - L q W‖ = ‖(L (q + s • W) - L q) W‖ := by
        rw [ContinuousLinearMap.sub_apply]
    _ ≤ ‖L (q + s • W) - L q‖ * ‖W‖ := ContinuousLinearMap.le_opNorm _ _
    _ ≤ ε * ‖W‖ := mul_le_mul_of_nonneg_right h1.le (norm_nonneg _)
end ReciprocityTheory.ChartRestriction.DS
