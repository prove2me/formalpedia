-- Prove2me | solution 1 for ProbabilityTheory.exists_nat_pow_lt_iInf
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-19T08:20:57.924876+00:00
-- url     : https://prove2.me/submissions/0889b78e-7095-4874-9c48-173dc10d2091

import Definitions.Def_BrownianMotion_Auxiliary_FiniteInf_F000
import Definitions.Def_BrownianMotion_Auxiliary_MeanInequalities_F000
import Definitions.Def_BrownianMotion_Continuity_Chaining_F001
import Definitions.Def_BrownianMotion_Continuity_HasBoundedInternalCoveringNumber_F001
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Order.CompleteLattice.Group
import Mathlib.Probability.Process.Kolmogorov
import Mathlib.Topology.EMetricSpace.PairReduction

/-
Copyright (c) 2025 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/

/-!
# Stochastic processes satisfying the Kolmogorov condition

-/

@[expose] public section

open MeasureTheory Metric
open scoped ENNReal NNReal Finset

section Aux

end Aux

namespace ProbabilityTheory

variable {T Ω E : Type*} [PseudoEMetricSpace T] {mΩ : MeasurableSpace Ω}
  [PseudoEMetricSpace E]
  {p q : ℝ} {M : ℝ≥0} {P : Measure Ω} {X : T → Ω → E}

section Measurability

variable [MeasurableSpace E] [BorelSpace E]

end Measurability

section FirstTerm

variable {J : Set T}

end FirstTerm

section SecondTerm

variable {J : Set T} {C : ℕ → Finset T} {ε : ℕ → ℝ≥0} {j k m : ℕ}

end SecondTerm

section Together

variable {M : ℝ≥0} {d p q : ℝ} {J : Set T} {c : ℝ≥0∞} {δ : ℝ≥0}

open Filter in
open scoped Topology in
theorem _root_.solution (hJ : Metric.ediam J < ∞) (hJ_finite : J.Finite)
    (hJ_nonempty : J.Nonempty) :
    ∃ k : ℕ, Metric.ediam J * 2⁻¹ ^ k < ⨅ (s : J) (t : J) (_h : 0 < edist s t), edist s t := by
  classical
  have hm : ∃ m : ℝ≥0∞, 0 < m ∧ ∀ s ∈ J, ∀ t ∈ J, 0 < edist s t → m ≤ edist s t := by
    set F := (hJ_finite.prod hJ_finite).toFinset.filter (fun p : T × T => 0 < edist p.1 p.2)
      with hF_def
    by_cases hF : F.Nonempty
    · obtain ⟨p, hp, hmin⟩ := F.exists_min_image (fun p => edist p.1 p.2) hF
      refine ⟨edist p.1 p.2, (Finset.mem_filter.1 hp).2, fun s hs t ht hst => hmin (s, t) ?_⟩
      simp [F, hs, ht, hst]
    · refine ⟨⊤, by simp, fun s hs t ht hst => absurd ⟨(s, t), ?_⟩ hF⟩
      simp [F, hs, ht, hst]
  obtain ⟨m, hm0, hmle⟩ := hm
  have hδ : m ≤ ⨅ (s : J) (t : J) (_h : 0 < edist s t), edist s t :=
    le_iInf fun s => le_iInf fun t => le_iInf fun h => hmle s s.2 t t.2 h
  have hlim : Tendsto (fun k : ℕ => Metric.ediam J * 2⁻¹ ^ k) atTop (𝓝 0) := by
    have := ENNReal.Tendsto.const_mul
      (ENNReal.tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (2⁻¹ : ℝ≥0∞) < 1))
      (Or.inr hJ.ne)
    simpa using this
  obtain ⟨k, hk⟩ := ((tendsto_order.1 hlim).2 m hm0).exists
  exact ⟨k, hk.trans_le hδ⟩

end Together

end ProbabilityTheory
