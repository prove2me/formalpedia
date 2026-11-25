-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.slm_mat_hint
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T12:41:45.858575+00:00
-- url     : https://prove2.me/submissions/df1e3dbc-7d9e-4f3c-aab0-4abd10f2bd0a

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_DiscreteSeriesExistence_CayleyChartDomainIsOpen
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_DiscreteSeriesExistence_ContDiffOnZeroOfContinuousOn
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_slmG_mat_apply

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
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {n : ℕ}
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
namespace ReciprocityTheory.ChartRestriction.DS
theorem _root_.solution {V : Set (Matrix (Fin n) (Fin n) ℂ)}
    {γ m : Matrix (Fin n) (Fin n) ℂ → Matrix (Fin n) (Fin n) ℂ} (Φ : (Matrix (Fin n) (Fin n) ℂ → ℂ) → Matrix (Fin n) (Fin n) ℂ → E)
    (P : (Matrix (Fin n) (Fin n) ℂ → ℂ) → Prop)
    (Op : Fin n → Fin n → (Matrix (Fin n) (Fin n) ℂ → ℂ) → (Matrix (Fin n) (Fin n) ℂ → ℂ))
    (hint : ∀ F, P F → ∀ q ∈ V, ∃ δ > 0, ∀ W : Matrix (Fin n) (Fin n) ℂ, ‖W‖ < δ → ∀ B : ℝ,
      (∀ s ∈ Ioc (0:ℝ) 1, ‖(∑ a, ∑ b, ((m (q + s • W) * fderiv ℝ γ (q + s • W) W) a b) •
          Φ (Op a b F) (q + s • W)) - ∑ a, ∑ b, ((m q * fderiv ℝ γ q W) a b) • Φ (Op a b F) q‖ ≤ B) →
      ‖Φ F (q + W) - Φ F q - ∑ a, ∑ b, ((m q * fderiv ℝ γ q W) a b) • Φ (Op a b F) q‖ ≤ B) :
    ∀ F, P F → ∀ q ∈ V, ∃ δ > 0, ∀ W : Matrix (Fin n) (Fin n) ℂ, ‖W‖ < δ → ∀ B : ℝ,
      (∀ s ∈ Ioc (0:ℝ) 1, ‖slmG (Y := Matrix (Fin n) (Fin n) ℂ) slmC (fderiv ℝ γ (q + s • W))
          (fun i => slmc m i (q + s • W) • Φ (Op i.1 i.2.1 F) (q + s • W)) W -
        slmG (Y := Matrix (Fin n) (Fin n) ℂ) slmC (fderiv ℝ γ q) (fun i => slmc m i q • Φ (Op i.1 i.2.1 F) q) W‖ ≤ B) →
      ‖Φ F (q + W) - Φ F q - slmG (Y := Matrix (Fin n) (Fin n) ℂ) slmC (fderiv ℝ γ q)
        (fun i => slmc m i q • Φ (Op i.1 i.2.1 F) q) W‖ ≤ B := by
  intro F hF q hq
  obtain ⟨δ, hδ, h⟩ := hint F hF q hq
  refine ⟨δ, hδ, fun W hW B hB => ?_⟩
  rw [slmG_mat_apply γ m q (fun a b => Φ (Op a b F) q) W]
  refine h W hW B fun s hs => ?_
  have h1 := hB s hs
  rwa [slmG_mat_apply γ m (q + s • W) (fun a b => Φ (Op a b F) (q + s • W)) W,
    slmG_mat_apply γ m q (fun a b => Φ (Op a b F) q) W] at h1
end ReciprocityTheory.ChartRestriction.DS
