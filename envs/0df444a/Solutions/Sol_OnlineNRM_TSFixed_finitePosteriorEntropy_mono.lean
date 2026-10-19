-- Prove2me | solution 1 for OnlineNRM.TSFixed.finitePosteriorEntropy_mono
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-17T18:35:43.698284+00:00
-- url     : https://prove2.me/submissions/19b10888-33dc-4be1-9942-615dc6afc8cf

import Definitions.Def_OnlineNRM_TSFixed_OracleEntropy
import Theorems.Thm_OnlineNRM_TSFixed_finitePosteriorEntropy_scalar_mono
import Theorems.Thm_OnlineNRM_TSFixed_finitePosteriorEntropy_sum

open MeasureTheory ProbabilityTheory
open scoped BigOperators

theorem solution
    {Ω α : Type*} [mΩ : MeasurableSpace Ω] [instα : Fintype α]
    (P : Measure Ω) [instP : IsProbabilityMeasure P]
    (m₁ m₂ : MeasurableSpace Ω) (hm : m₁ ≤ m₂)
    (w : Ω → α → ℝ)
    (hwmeas : ∀ a, @Measurable Ω ℝ mΩ inferInstance (fun ω => w ω a))
    (hw0 : ∀ ω a, 0 ≤ w ω a)
    (hwsum : ∀ ω, ∑ a : α, w ω a = 1) :
    @ProbabilityTheory.finitePosteriorEntropy Ω α mΩ inferInstance P m₂ w ≤
      @ProbabilityTheory.finitePosteriorEntropy Ω α mΩ inferInstance P m₁ w := by
  have hwle : ∀ ω a, w ω a ≤ 1 := by
    intro ω a
    rw [← hwsum ω]
    exact Finset.single_le_sum (fun b hb => hw0 ω b) (Finset.mem_univ a)
  -- Keep the ambient measurable space fixed in both finite-sum rewrites.
  rw [@OnlineNRM.TSFixed.finitePosteriorEntropy_sum Ω α mΩ instα P instP
        m₂ w hwmeas hw0 hwsum,
      @OnlineNRM.TSFixed.finitePosteriorEntropy_sum Ω α mΩ instα P instP
        m₁ w hwmeas hw0 hwsum]
  exact Finset.sum_le_sum fun a _ =>
    @OnlineNRM.TSFixed.finitePosteriorEntropy_scalar_mono Ω mΩ P instP
      m₁ m₂ hm (fun ω => w ω a) (hwmeas a)
      (fun ω => hw0 ω a) (fun ω => hwle ω a)