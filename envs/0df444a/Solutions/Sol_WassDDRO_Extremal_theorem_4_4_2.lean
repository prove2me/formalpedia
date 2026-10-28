-- Prove2me | solution 2 for WassDDRO.Extremal.theorem_4_4
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-26T14:59:42.765912+00:00
-- url     : https://prove2.me/submissions/6b80e2b0-9226-4afd-8075-c4344f1b6f4e

import Mathlib
import Definitions.Def_WassDDRO_Extremal_Setting
import Definitions.Def_WassDDRO_Reduction_Setting
import Theorems.Thm_WassDDRO_Reduction_worstCase_eq_program12f
import Theorems.Thm_WassDDRO_Extremal_program12f_eq_program13
import Theorems.Thm_WassDDRO_Extremal_discreteQ_mem_ball
import Theorems.Thm_WassDDRO_Extremal_objective13_le_expect

set_option autoImplicit false
open WassDDRO.Extremal Filter Topology MeasureTheory

-- carved from submission 9d9b1da1-23a8-4b1d-b0ad-3d6a8366c2eb, lines 3325-3370

theorem solution {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E]
    {K N : ℕ} (hK : 0 < K) (hN : 0 < N) (Ξ : Set E) (ℓ : Fin K → E → EReal)
    (hmeas : ∀ k, Measurable (ℓ k)) (ξhat : Fin N → E) (hξ : ∀ i, ξhat i ∈ Ξ)
    (ε : ℝ) (hε : 0 ≤ ε) (hA : Assumption41 Ξ ℓ) :
    worstCaseExpectation ε Ξ ξhat (maxLoss ℓ) = program13Value ε Ξ ξhat ℓ ∧
    ∀ (α : ℕ → Fin N → Fin K → ℝ) (q : ℕ → Fin N → Fin K → E),
      (∀ r, Feasible13 ε Ξ ξhat (α r) (q r)) →
      Tendsto (fun r => objective13 ξhat ℓ (α r) (q r)) atTop
        (𝓝 (program13Value ε Ξ ξhat ℓ)) →
      (∀ r, discreteQ ξhat (α r) (q r) ∈ WassersteinDRO.Duality.ambiguitySet ε 1 Ξ
          (WassersteinDRO.Duality.empiricalDistribution ξhat)) ∧
      Tendsto (fun r => DupacovaWets.Consistency.expect (discreteQ ξhat (α r) (q r)) (maxLoss ℓ)) atTop
        (𝓝 (worstCaseExpectation ε Ξ ξhat (maxLoss ℓ))) ∧
      Tendsto (fun r => ((1 / (N : ℝ) : ℝ) : EReal) *
          ∑ i, ∑ k, term13 (maxLoss ℓ) (ξhat i) (α r i k) (q r i k)) atTop
        (𝓝 (worstCaseExpectation ε Ξ ξhat (maxLoss ℓ))) := by
  -- Assumption 4.1 is the same structure in both namespaces, field for field.
  have hAR : WassDDRO.Reduction.Assumption41 Ξ ℓ :=
    ⟨hA.convex, hA.closed, hA.ne_top, hA.convex_epigraph, hA.lsc, hA.not_bot_on⟩
  have h12f : worstCaseExpectation ε Ξ ξhat (maxLoss ℓ) = program12fValue ε Ξ ξhat ℓ :=
    WassDDRO.Reduction.worstCase_eq_program12f hK hN Ξ ℓ hmeas ξhat hξ ε hε hAR
  have hv : worstCaseExpectation ε Ξ ξhat (maxLoss ℓ) = program13Value ε Ξ ξhat ℓ :=
    h12f.trans (program12f_eq_program13 hK hN Ξ ℓ hmeas ξhat hξ ε hε hA)
  refine ⟨hv,?_⟩
  intro α q hf ht
  have hm : ∀ r, discreteQ ξhat (α r) (q r) ∈ WassersteinDRO.Duality.ambiguitySet ε 1 Ξ
      (WassersteinDRO.Duality.empiricalDistribution ξhat) :=
    fun r => discreteQ_mem_ball hN Ξ ξhat hξ ε (α r) (q r) (hf r)
  have hlo : ∀ r, objective13 ξhat ℓ (α r) (q r) ≤
      DupacovaWets.Consistency.expect (discreteQ ξhat (α r) (q r)) (maxLoss ℓ) :=
    fun r => (objective13_le_expect hN Ξ ℓ hmeas hA.ne_top ξhat ε (α r) (q r) (hf r)).2
  have hhi : ∀ r, DupacovaWets.Consistency.expect (discreteQ ξhat (α r) (q r)) (maxLoss ℓ) ≤
      worstCaseExpectation ε Ξ ξhat (maxLoss ℓ) :=
    fun r => le_iSup₂_of_le (discreteQ ξhat (α r) (q r)) (hm r) le_rfl
  rw [←hv] at ht
  have hto : Tendsto (fun r => DupacovaWets.Consistency.expect (discreteQ ξhat (α r) (q r)) (maxLoss ℓ))
      atTop (𝓝 (worstCaseExpectation ε Ξ ξhat (maxLoss ℓ))) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le ht tendsto_const_nhds hlo hhi
  refine ⟨hm,hto,?_⟩
  have he : (fun r => ((1 / (N : ℝ) : ℝ) : EReal) *
      ∑ i, ∑ k, term13 (maxLoss ℓ) (ξhat i) (α r i k) (q r i k)) =
      (fun r => DupacovaWets.Consistency.expect (discreteQ ξhat (α r) (q r)) (maxLoss ℓ)) :=
    funext (fun r => (objective13_le_expect hN Ξ ℓ hmeas hA.ne_top ξhat ε
      (α r) (q r) (hf r)).1.symm)
  rw [he]
  exact hto
