-- Prove2me | solution 1 for PositivityTheory.CW.WeightedEigenSum.wsum_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T11:33:01.063337+00:00
-- url     : https://prove2.me/submissions/37c8ed49-d182-4103-9d52-0cf7efd9fdff

import Definitions.Def_Development_WeilBound_CoreStatements_PublishedTheorems_CasselmanWallach_FunctionalCalculusLaws
import Definitions.Def_Development_WeilBound_CoreStatements_PublishedTheorems_CasselmanWallach_KFiniteInclusion

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix Finset ReciprocityTheory.ChartRestriction.DS
open PositivityTheory PositivityTheory.CW
open PositivityTheory.CW.WeightedEigenSum
namespace PositivityTheory.CW.WeightedEigenSum
theorem _root_.solution {ι : Type} (μ : ι → ℝ) (hnn : ∀ i, 0 ≤ μ i) (hfin : ∀ R : ℝ, {i | μ i ≤ R}.Finite)
    (a : ι → ℝ) (ha : ∀ i, 0 ≤ a i) (s : ℕ) (hs : 1 ≤ s) (K : ℝ)
    (hS : ∀ (R : ℝ) (S : Finset ι), (∀ i, i ∈ S ↔ μ i < R) → ∑ i ∈ S, phiR s R (μ i) * a i ≤ K ^ 2)
    (T : Finset ι) : ∑ i ∈ T, ((1 + μ i) ^ s)⁻¹ * a i ≤ K ^ 2 := by
  obtain ⟨R0, hR0⟩ : ∃ R0 : ℝ, ∀ i ∈ T, μ i < R0 :=
    ⟨∑ i ∈ T, μ i + 1, fun i hi => by
      have := Finset.single_le_sum (fun j _ => hnn j) hi
      linarith⟩
  have key : ∀ R : ℝ, R0 ≤ R →
      ∑ i ∈ T, ((1 + μ i) ^ s)⁻¹ * a i - ((1 + R) ^ s)⁻¹ * ∑ i ∈ T, a i ≤ K ^ 2 := by
    intro R hR
    have hSmem : ∀ i, i ∈ (hfin R).toFinset.filter (fun i => μ i < R) ↔ μ i < R := by
      intro i
      simp only [Finset.mem_filter, Set.Finite.mem_toFinset, Set.mem_ofPred_eq]
      exact ⟨fun h => h.2, fun h => ⟨h.le, h⟩⟩
    have hTS : T ⊆ (hfin R).toFinset.filter (fun i => μ i < R) :=
      fun i hi => (hSmem i).mpr (lt_of_lt_of_le (hR0 i hi) hR)
    have h1 := hS R _ hSmem
    have h2 : ∑ i ∈ T, phiR s R (μ i) * a i ≤
        ∑ i ∈ (hfin R).toFinset.filter (fun i => μ i < R), phiR s R (μ i) * a i :=
      Finset.sum_le_sum_of_subset_of_nonneg hTS (fun i _ _ => mul_nonneg (le_max_right _ _) (ha i))
    have h3 : ∑ i ∈ T, phiR s R (μ i) * a i =
        ∑ i ∈ T, ((1 + μ i) ^ s)⁻¹ * a i - ((1 + R) ^ s)⁻¹ * ∑ i ∈ T, a i := by
      rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun i hi => ?_
      have hlt : ((1 + R) ^ s)⁻¹ ≤ ((1 + μ i) ^ s)⁻¹ := by
        apply inv_anti₀ (pow_pos (by linarith [hnn i]) s)
        exact pow_le_pow_left₀ (by linarith [hnn i]) (by linarith [hR0 i hi]) s
      rw [phiR, max_eq_left (by linarith)]
      ring
    linarith
  have hpow : Filter.Tendsto (fun R : ℝ => (1 + R) ^ s) Filter.atTop Filter.atTop :=
    (Filter.tendsto_pow_atTop (by omega : s ≠ 0)).comp
      (Filter.tendsto_atTop_add_const_left _ 1 Filter.tendsto_id)
  have ht : Filter.Tendsto
      (fun R : ℝ => ∑ i ∈ T, ((1 + μ i) ^ s)⁻¹ * a i - ((1 + R) ^ s)⁻¹ * ∑ i ∈ T, a i) Filter.atTop
      (nhds (∑ i ∈ T, ((1 + μ i) ^ s)⁻¹ * a i - 0 * ∑ i ∈ T, a i)) :=
    tendsto_const_nhds.sub ((tendsto_inv_atTop_zero.comp hpow).mul_const _)
  have hlim := le_of_tendsto ht (Filter.eventually_atTop.mpr ⟨R0, key⟩)
  simpa using hlim
end PositivityTheory.CW.WeightedEigenSum
