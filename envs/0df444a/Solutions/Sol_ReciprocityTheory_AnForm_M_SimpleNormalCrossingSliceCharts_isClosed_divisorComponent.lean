-- Prove2me | solution 1 for ReciprocityTheory.AnForm.M.SimpleNormalCrossingSliceCharts.isClosed_divisorComponent
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T15:41:52.299707+00:00
-- url     : https://prove2.me/submissions/8b426c2d-4219-498a-bdb5-b7c3613ed217

import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_IsPotentialPullbackStatement
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_SNCAtlas

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M
open MeasureTheory FinHolAtlas Topology Filter Set
open scoped ContDiff
noncomputable section
open ReciprocityTheory.AnForm.M.SimpleNormalCrossingSliceCharts
variable {X : Type} [TopologicalSpace X]
namespace ReciprocityTheory.AnForm.M.SimpleNormalCrossingSliceCharts
theorem _root_.solution {e : ℕ} (A : FinHolAtlas e X) (L : LocPot X) (s : X → X → ℂ) {r : ℕ}
    (m : Fin r → ℕ) (W : Fin r → Set X) (h : IsSNC A L s m W) (k : Fin r) : IsClosed (W k) := by
  rw [← isOpen_compl_iff, isOpen_iff_forall_mem_open]
  intro x hx
  obtain ⟨ψ, -, hxψ, -, σ, -, hW, -⟩ := h x
  have hWk := hW k
  cases hσ : σ k with
  | none =>
    refine ⟨ψ.source, ?_, ψ.open_source, hxψ⟩
    intro y hy hyW
    have hm : y ∈ W k ∩ ψ.source := ⟨hyW, hy⟩
    rw [hWk] at hm
    obtain ⟨i, hi, -⟩ := hm.2
    rw [hσ] at hi
    exact absurd hi (by simp)
  | some i =>
    refine ⟨ψ.source ∩ ψ ⁻¹' {v | v i ≠ 0}, ?_, ?_, ?_⟩
    · rintro y ⟨hy, hyi⟩ hyW
      have hm : y ∈ W k ∩ ψ.source := ⟨hyW, hy⟩
      rw [hWk] at hm
      obtain ⟨j, hj, hj0⟩ := hm.2
      rw [hσ, Option.some.injEq] at hj
      rw [← hj] at hj0
      exact hyi hj0
    · exact ψ.continuousOn.isOpen_inter_preimage ψ.open_source
        (isOpen_ne_fun (continuous_apply i) continuous_const)
    · refine ⟨hxψ, ?_⟩
      intro hxi
      have hm : x ∈ {y ∈ ψ.source | ∃ j, σ k = some j ∧ ψ y j = 0} := ⟨hxψ, i, hσ, hxi⟩
      rw [← hWk] at hm
      exact hx hm.1
end ReciprocityTheory.AnForm.M.SimpleNormalCrossingSliceCharts
