-- Prove2me | solution 1 for PI.QuotMeasUniqW.hAvg_indicator_le
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:43:26.488544+00:00
-- url     : https://prove2.me/submissions/4285ffd5-762f-4c81-8d87-8256b1677bf9

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_QuotientMeasureUniqueness_QmuWeight
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_QuotientMeasureUniqueness_QLiftIsMulLeftInvariant
import Theorems.Thm_PI_QuotMeasUniqW_indicator_preimage_one
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
noncomputable section
open MeasureTheory Pointwise
open scoped ENNReal
namespace PI.QuotMeasUniqW
private theorem lintegral_indicator_one_le' {α : Type*} [MeasurableSpace α] (μ : Measure α)
    (S : Set α) : ∫⁻ a, S.indicator 1 a ∂μ ≤ μ S := by
  exact lintegral_indicator_one_le S
end PI.QuotMeasUniqW
end
end

set_option autoImplicit false
noncomputable section
open MeasureTheory Pointwise
open scoped ENNReal
open PI PI.QuotMeasUniqW
namespace PI.QuotMeasUniqW
theorem _root_.solution {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G] [BorelSpace G] {H : Subgroup G}
    (ν : Measure H) [ν.IsMulLeftInvariant] (C K : Set G) (d g : G) (hC : ∀ x ∈ C, d⁻¹ * x ∈ K) :
    hAvg ν (C.indicator 1) g ≤ ν {h : H | (h : G) ∈ K⁻¹ * K} := by
  have hint_r : hAvg ν (C.indicator 1) g
      = ∫⁻ h, ((fun h : H => g * (h : G)) ⁻¹' C).indicator 1 h ∂ν := by
    unfold hAvg
    exact lintegral_congr fun h => (indicator_preimage_one (fun h : H => g * (h : G)) C h).symm
  rw [hint_r]
  refine (lintegral_indicator_one_le' ν _).trans ?_
  rcases ((fun h : H => g * (h : G)) ⁻¹' C).eq_empty_or_nonempty with h0 | ⟨h1, hh1⟩
  · rw [h0]; simp
  · have hsub : (fun h : H => g * (h : G)) ⁻¹' C
        ⊆ (fun h : H => h1⁻¹ * h) ⁻¹' {h : H | (h : G) ∈ K⁻¹ * K} := by
      intro h hh
      simp only [Set.mem_preimage, Set.mem_ofPred_eq, Subgroup.coe_mul, Subgroup.coe_inv]
      have a1 : d⁻¹ * (g * (h1 : G)) ∈ K := hC (g * (h1 : G)) hh1
      have a2 : d⁻¹ * (g * (h : G)) ∈ K := hC (g * (h : G)) hh
      have e : (h1 : G)⁻¹ * (h : G) = (d⁻¹ * (g * (h1 : G)))⁻¹ * (d⁻¹ * (g * (h : G))) := by
        group
      rw [e]
      exact Set.mul_mem_mul (Set.inv_mem_inv.2 a1) a2
    calc ν ((fun h : H => g * (h : G)) ⁻¹' C)
        ≤ ν ((fun h : H => h1⁻¹ * h) ⁻¹' {h : H | (h : G) ∈ K⁻¹ * K}) := measure_mono hsub
      _ = ν {h : H | (h : G) ∈ K⁻¹ * K} := by
        exact measure_preimage_mul ν h1⁻¹ _
end PI.QuotMeasUniqW
