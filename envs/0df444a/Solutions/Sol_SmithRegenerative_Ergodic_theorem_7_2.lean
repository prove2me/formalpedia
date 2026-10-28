-- Prove2me | solution 2 for SmithRegenerative.Ergodic.theorem_7
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-26T16:32:06.020888+00:00
-- url     : https://prove2.me/submissions/8882378f-d4e9-41b9-85f5-397d0123b538

import Mathlib
import Definitions.Def_SmithRegenerative_Ergodic_Renewal
import Definitions.Def_SmithRegenerative_Ergodic_CumulativeProcess
import Theorems.Thm_SmithRegenerative_Ergodic_lemma_8
import Theorems.Thm_SmithRegenerative_Ergodic_regeneration_limit

set_option autoImplicit false
open MeasureTheory ProbabilityTheory Filter Topology
open SmithRegenerative.Ergodic

-- carved from submission adeac120-cf30-4825-8b46-ef071256c5e5, lines 526-546

theorem solution {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    (t : ℕ → Ω → ℝ) (w : ℝ → Ω → ℝ) (hren : IsRenewalProcess P t)
    (ht0 : ∀ ω, t 0 ω = 0) (hw0 : ∀ ω, w 0 ω = 0) (hμ : Integrable (t 1) P)
    (hcum : IsCumulativeProcess P t w) (hκ : Integrable (cycleVariation t w 1) P) :
    ∀ᵐ ω ∂P, Tendsto (fun s : ℝ => w s ω / s) atTop
      (𝓝 ((∫ ω, cycleIncrement t w 1 ω ∂P) / ∫ ω, t 1 ω ∂P)) := by
  have hκ1 : Integrable (fun ω => cycleVariation t w 1 ω ^ (1 : ℝ)) P := by
    simpa [Real.rpow_one] using hκ
  filter_upwards [SmithRegenerative.Ergodic.regeneration_limit t w hren ht0 hw0 hμ hcum hκ,
    SmithRegenerative.Ergodic.lemma_8 t w hren ht0 hμ hcum 1 one_pos hκ1] with ω h1 h2
  have h3 := h1.sub h2
  rw [sub_zero] at h3
  refine h3.congr fun s => ?_
  simp only [div_one, Real.rpow_one]
  ring
