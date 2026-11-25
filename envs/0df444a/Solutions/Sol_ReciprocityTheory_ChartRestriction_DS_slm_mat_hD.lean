-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.slm_mat_hD
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T12:52:33.582836+00:00
-- url     : https://prove2.me/submissions/b159de3e-7dd3-4e13-b10b-0d423d6607ad

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_DiscreteSeriesExistence_CayleyChartDomainIsOpen
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_DiscreteSeriesExistence_ContDiffOnZeroOfContinuousOn
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_slm_gen_hD
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_slmc_cd
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_slm_mat_hint

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
theorem _root_.solution {V : Set (Matrix (Fin n) (Fin n) ℂ)} (hV : IsOpen V)
    {γ m : Matrix (Fin n) (Fin n) ℂ → Matrix (Fin n) (Fin n) ℂ} (hγ : ContDiffOn ℝ ∞ γ V)
    (hm : ContDiffOn ℝ ∞ m V) (Φ : (Matrix (Fin n) (Fin n) ℂ → ℂ) → Matrix (Fin n) (Fin n) ℂ → E)
    (P : (Matrix (Fin n) (Fin n) ℂ → ℂ) → Prop)
    (Op : Fin n → Fin n → (Matrix (Fin n) (Fin n) ℂ → ℂ) → (Matrix (Fin n) (Fin n) ℂ → ℂ))
    (hP : ∀ F, P F → ∀ a b, P (Op a b F))
    (hcont : ∀ F, P F → ContinuousOn (Φ F) V)
    (hint : ∀ F, P F → ∀ q ∈ V, ∃ δ > 0, ∀ W : Matrix (Fin n) (Fin n) ℂ, ‖W‖ < δ → ∀ B : ℝ,
      (∀ s ∈ Ioc (0:ℝ) 1, ‖(∑ a, ∑ b, ((m (q + s • W) * fderiv ℝ γ (q + s • W) W) a b) •
          Φ (Op a b F) (q + s • W)) - ∑ a, ∑ b, ((m q * fderiv ℝ γ q W) a b) • Φ (Op a b F) q‖ ≤ B) →
      ‖Φ F (q + W) - Φ F q - ∑ a, ∑ b, ((m q * fderiv ℝ γ q W) a b) • Φ (Op a b F) q‖ ≤ B)
    (F : Matrix (Fin n) (Fin n) ℂ → ℂ) (hF : P F) (q : Matrix (Fin n) (Fin n) ℂ) (hq : q ∈ V) :
    HasFDerivAt (Φ F) (slmG (Y := Matrix (Fin n) (Fin n) ℂ) slmC (fderiv ℝ γ q)
      (fun i => slmc m i q • Φ (Op i.1 i.2.1 F) q)) q :=
  slm_gen_hD hV hγ slmC (fun i => slmc m i) (fun i => slmc_cd hm i) P (fun i => Op i.1 i.2.1)
    (fun F hF i => hP F hF i.1 i.2.1) Φ hcont (slm_mat_hint Φ P Op hint) F hF q hq
end ReciprocityTheory.ChartRestriction.DS
