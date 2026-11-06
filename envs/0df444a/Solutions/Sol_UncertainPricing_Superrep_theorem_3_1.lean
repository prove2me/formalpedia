-- Prove2me | solution 1 for UncertainPricing.Superrep.theorem_3_1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-05T18:48:30.734262+00:00
-- url     : https://prove2.me/submissions/1616db46-653a-43a6-b5e8-4a0f1e6bae15
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_UncertainPricing_Superrep_Setting
import Definitions.Def_UncertainPricing_Superrep_Compact
import Theorems.Thm_UncertainPricing_Superrep_theorem_3_1_gamma
import Theorems.Thm_UncertainPricing_Superrep_lemma_5_4
import Theorems.Thm_UncertainPricing_Superrep_lemma_5_5
import Theorems.Thm_UncertainPricing_Superrep_lemma_5_6

open MeasureTheory Filter Topology BoundedContinuousFunction
open UncertainPricing.Superrep

theorem solution (T : ℝ) (hT : 0 < T) (μL μU : StieltjesFunction ℝ) (hμL : IsDistFn T μL)
    (hμU : IsDistFn T μU) (Ps : Set (Measure (Ω T)))
    (hPs : ∀ P ∈ Ps, IsMartingaleMeasure P ∧ HypLU μL μU P)
    (hHol : IsHolder T μU) :
    ∃ P'' : Set (Measure (Ω T)), (∀ P ∈ P'', IsMartingaleMeasure P ∧ HypLU μL μU P) ∧
      ∀ f : Ω T →ᵇ ℝ, InClaimFamilies f → Lam Ps μU f = supE P'' f := by
  -- `H(μ̲, μ̄)` implies `H(μ̄)`
  have hPsU : ∀ P ∈ Ps, IsMartingaleMeasure P ∧ HypU μU P := by
    intro P hP
    obtain ⟨hm, A, hA, hAe⟩ := hPs P hP
    exact ⟨hm, A, hA, hAe.mono fun ω h s t hst => (h s t hst).2⟩
  obtain ⟨P'', hP'', hΓ⟩ := theorem_3_1_gamma T hT μL μU hμL hμU Ps hPs hHol
  refine ⟨P'', hP'', fun f hf => hΓ f ?_⟩
  rcases hf with h | h | h
  · exact lemma_5_4 T hT μU hμU Ps hPsU hHol f h
  · exact lemma_5_5 T hT μU hμU Ps hPsU hHol f h
  · exact lemma_5_6 T hT μU hμU Ps hPsU hHol f h
