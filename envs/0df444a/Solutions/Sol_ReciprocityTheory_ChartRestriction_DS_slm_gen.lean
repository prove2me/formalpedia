-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.slm_gen
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T12:58:15.859038+00:00
-- url     : https://prove2.me/submissions/89fb5209-f282-4628-a514-e8f80264e8d5

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_DiscreteSeriesExistence_CayleyChartDomainIsOpen
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_DiscreteSeriesExistence_ContDiffOnZeroOfContinuousOn
import Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_DS_slm_le_inf__d72d3bf390d4
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_slmG_cd
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_contDiffOn_zero_of_continuousOn
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_slm_gen_hD

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
    ∀ F, P F → ContDiffOn ℝ ∞ (Φ F) V := by
  intro F hF
  have key : ∀ N : ℕ, ∀ F, P F → ContDiffOn ℝ N (Φ F) V := by
    intro N
    induction N with
    | zero => intro F hF; exact contDiffOn_zero_of_continuousOn (hcont F hF)
    | succ N ih =>
      intro F hF
      have hD := slm_gen_hD hV hγ C c hc P Op hP Φ hcont hint F hF
      have hw : ∀ i, ContDiffOn ℝ N (fun q => c i q • Φ (Op i F) q) V := fun i =>
        ((hc i).of_le (slm_le_inf' N)).smul (ih (Op i F) (hP F hF i))
      have hfd : ContDiffOn ℝ N (fderiv ℝ (Φ F)) V :=
        (slmG_cd hV hγ C hw).congr fun q hq => (hD q hq).fderiv
      rw [Nat.cast_succ, contDiffOn_succ_iff_fderiv_of_isOpen hV]
      exact ⟨fun q hq => (hD q hq).differentiableAt.differentiableWithinAt, by simp, hfd⟩
  exact contDiffOn_infty.mpr fun N => key N F hF
end ReciprocityTheory.ChartRestriction.DS
