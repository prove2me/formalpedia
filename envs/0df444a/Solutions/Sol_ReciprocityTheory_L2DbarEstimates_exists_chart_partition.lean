-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.exists_chart_partition
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T14:45:07.846281+00:00
-- url     : https://prove2.me/submissions/c6519223-b679-4cd6-a74f-4352a8ee78b2

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_TsupportDbSubset
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_ExistsChartPartition
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_smoothR_const
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_smoothR_prod
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_exists_chart_bump
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_CkR_add
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_CkR_mul
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Ck_add
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Ck_mul
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Holo_add
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Holo_mul
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_SmoothR_add
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_SmoothR_mul
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Smooth_add
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Smooth_mul


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.L2DbarEstimates
open MeasureTheory Filter Topology Set
open scoped ContDiff ENNReal
noncomputable section
namespace ReciprocityTheory.L2DbarEstimates
theorem _root_.solution {M : Type*} [TopologicalSpace M] [T2Space M] (n : ℕ) (z : M → V n) (hz : IsLocalHomeomorph z) (K U : Set M) (hK : IsCompact K) (hU : IsOpen U) (hKU : K ⊆ U) :
    ∃ (N : ℕ) (e : Fin N → OpenPartialHomeomorph M (V n)) (χ : Fin N → M → ℝ),
      (∀ i, IsChart n z (e i)) ∧ (∀ i, SmoothR n z (χ i)) ∧ (∀ i, HasCompactSupport (χ i)) ∧
      (∀ i, tsupport (χ i) ⊆ (e i).source ∩ U) ∧ (∀ i x, 0 ≤ χ i x) ∧
      (∀ x, ∑ i, χ i x ≤ 1) ∧ (∀ x ∈ K, ∑ i, χ i x = 1) := by
  classical
  have hz' : ∀ y, ∃ e : OpenPartialHomeomorph M (V n), y ∈ e.source ∧ z = e := hz
  have H : ∀ x, ∃ (e : OpenPartialHomeomorph M (V n)) (ψ : M → ℝ), x ∈ U →
      IsChart n z e ∧ SmoothR n z ψ ∧ HasCompactSupport ψ ∧ tsupport ψ ⊆ e.source ∩ U ∧
      (∀ y, 0 ≤ ψ y ∧ ψ y ≤ 1) ∧ ∀ᶠ y in 𝓝 x, ψ y = 1 := by
    intro x
    by_cases hx : x ∈ U
    · obtain ⟨e, ψ, h⟩ := exists_chart_bump n z hz U hU x hx
      exact ⟨e, ψ, fun _ => h⟩
    · obtain ⟨e0, -, -⟩ := hz' x
      exact ⟨e0, fun _ => 0, fun h => absurd h hx⟩
  choose e ψ hψ using H
  obtain ⟨t, htK, hcov⟩ := hK.elim_nhds_subcover (fun x => {y | ψ x y = 1})
    (fun x hx => (hψ x (hKU hx)).2.2.2.2.2)
  let g : Fin t.card → M := fun i => (t.equivFin.symm i : M)
  have hgU : ∀ i, g i ∈ U := fun i => hKU (htK _ (t.equivFin.symm i).2)
  have P := fun i => hψ (g i) (hgU i)
  have h1 : ∀ j, SmoothR n z (fun y => 1 - ψ (g j) y) := by
    intro j
    have h2 := SmoothR.add n z _ _ (smoothR_const n z 1)
      (SmoothR.mul n z _ _ (smoothR_const n z (-1)) (P j).2.1)
    have h3 : (fun y => 1 - ψ (g j) y) = fun y => 1 + (-1) * ψ (g j) y := by funext y; ring
    rw [h3]; exact h2
  have hsum : ∀ y, ∑ i, ψ (g i) y * ∏ j ∈ Finset.univ.filter (fun j => j < i), (1 - ψ (g j) y) =
      1 - ∏ i, (1 - ψ (g i) y) := by
    intro y
    have h4 := Finset.prod_one_sub_ordered (Finset.univ : Finset (Fin t.card)) (fun i => ψ (g i) y)
    beta_reduce at h4
    linarith
  have hprod : ∀ y, 0 ≤ ∏ i, (1 - ψ (g i) y) :=
    fun y => Finset.prod_nonneg fun j _ => sub_nonneg.2 ((P j).2.2.2.2.1 y).2
  refine ⟨t.card, fun i => e (g i),
    fun i y => ψ (g i) y * ∏ j ∈ Finset.univ.filter (fun j => j < i), (1 - ψ (g j) y),
    fun i => (P i).1, fun i => ?_, fun i => ?_, fun i => ?_, fun i x => ?_, fun x => ?_,
    fun x hx => ?_⟩
  · exact SmoothR.mul n z _ _ (P i).2.1
      (smoothR_prod n z (Finset.univ.filter (fun j => j < i)) (fun j y => 1 - ψ (g j) y)
        (fun j _ => h1 j))
  · exact HasCompactSupport.mul_right
      (f' := fun y => ∏ j ∈ Finset.univ.filter (fun j => j < i), (1 - ψ (g j) y)) (P i).2.2.1
  · exact tsupport_mul_subset_left.trans (P i).2.2.2.1
  · exact mul_nonneg ((P i).2.2.2.2.1 x).1
      (Finset.prod_nonneg fun j _ => sub_nonneg.2 ((P j).2.2.2.2.1 x).2)
  · rw [hsum x]
    linarith [hprod x]
  · rw [hsum x]
    obtain ⟨x', hx't, hx'⟩ := Set.mem_iUnion₂.1 (hcov hx)
    have hi : g (t.equivFin ⟨x', hx't⟩) = x' := by simp [g]
    have h0 : ∏ i, (1 - ψ (g i) x) = 0 := by
      apply Finset.prod_eq_zero (Finset.mem_univ (t.equivFin ⟨x', hx't⟩))
      simp only [Set.mem_setOf_eq] at hx'
      rw [hi, hx', sub_self]
    rw [h0, sub_zero]
end ReciprocityTheory.L2DbarEstimates
