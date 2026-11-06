-- Prove2me | solution 1 for ProbabilityTheory.ae_finite_support_pieceSum
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T10:37:29.017281+00:00
-- url     : https://prove2.me/submissions/c6a8f232-7b74-4a89-92c3-289d07327534

import Definitions.Def_LeanLevy_RandomMeasure_TimeSpacePoisson
import Theorems.Thm_ProbabilityTheory_ae_finite_pieces_mem
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.MeasureTheory.MeasurableSpace.Defs
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Filter Set Topology Complex
open scoped NNReal ENNReal BigOperators
variable {Ω : Type} [MeasurableSpace Ω] {ν : Measure ℝ} [SigmaFinite ν]
  {K : ℕ → Ω → ℕ} {X : ℕ → ℕ → Ω → ℝ × ℝ} {μ : Measure Ω}

theorem solution [IsProbabilityMeasure μ]
    (hd : IsPoissonPointFamily K X ((volume : Measure ℝ).prod ν) μ)
    {R : Set (ℝ × ℝ)} (hR : MeasurableSet R)
    (hRfin : ((volume : Measure ℝ).prod ν) R < ⊤)
    {g : ℝ × ℝ → ℝ} (hg : ∀ p ∉ R, g p = 0) :
    ∀ᵐ ω ∂μ, {k | pieceSum K X g k ω ≠ 0}.Finite := by
  filter_upwards [ae_finite_pieces_mem hd hR hRfin] with ω hω
  refine hω.subset fun k hk => ?_
  simp only [Set.mem_setOf_eq] at hk ⊢
  have hk' : (∑ n ∈ Finset.range (K k ω), g (X k n ω)) ≠ 0 := hk
  obtain ⟨n, hn, hterm⟩ := Finset.exists_ne_zero_of_sum_ne_zero hk'
  refine ⟨n, hn, ?_⟩
  by_contra hnm
  exact hterm (hg _ hnm)
