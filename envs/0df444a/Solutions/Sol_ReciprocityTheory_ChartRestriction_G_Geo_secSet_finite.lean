-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Geo.secSet_finite
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:21:36.443855+00:00
-- url     : https://prove2.me/submissions/dbc68331-a841-49c8-bfcc-ee2bcf76043f

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterSt
import Definitions.Def_ReciprocityTheory_AnalyticForms_AnalyticCharts_NullZero
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterOsgood
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterSheetB
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_coincide_null

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo
open MeasureTheory Metric Filter Topology
variable {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)] {e : ℕ}
namespace ReciprocityTheory.ChartRestriction.G.Geo
theorem _root_.solution (hA : OsgoodStatement) {P : Ideal (MRing ι)}
    {Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)} (hfin : ∀ y, (fibre P Ψ y).Finite)
    (c : Fin e → ℂ) {r : ℝ} (hr : 0 < r) : (secSet P Ψ (ball c r)).Finite := by
  by_contra hinf
  have hS : (secSet P Ψ (ball c r)).Infinite := hinf
  have key : ∀ m : ℕ, volume {y | y ∈ ball c r ∧ (fibre P Ψ y).ncard < m} = 0 := by
    intro m
    obtain ⟨F, hFS, hFc⟩ := hS.exists_subset_card_eq m
    have hnull : volume (⋃ G ∈ (↑F : Set ((Fin e → ℂ) → ((k : K) → ι k) → ℂ)), ⋃ G' ∈ (↑F : Set ((Fin e → ℂ) → ((k : K) → ι k) → ℂ)),
        {y | G ≠ G' ∧ y ∈ ball c r ∧ G y = G' y}) = 0 := by
      refine (measure_biUnion_null_iff (Finset.countable_toSet F)).2 fun G hG =>
        (measure_biUnion_null_iff (Finset.countable_toSet F)).2 fun G' hG' => ?_
      by_cases h : G = G'
      · simp [h]
      · refine measure_mono_null ?_ (coincide_null hA (hFS hG) (hFS hG') h)
        intro y hy
        exact ⟨hy.2.1, hy.2.2⟩
    refine measure_mono_null (fun y hy => ?_) hnull
    obtain ⟨hyb, hlt⟩ := hy
    by_contra hnot
    have hinj : Set.InjOn (fun G : ((Fin e → ℂ) → ((k : K) → ι k) → ℂ) => G y) (↑F : Set ((Fin e → ℂ) → ((k : K) → ι k) → ℂ)) := fun G hG G' hG' heq => by
      by_contra hne
      exact hnot (Set.mem_iUnion₂.2 ⟨G, hG, Set.mem_iUnion₂.2 ⟨G', hG', ⟨hne, hyb, heq⟩⟩⟩)
    have hmaps : Set.MapsTo (fun G : ((Fin e → ℂ) → ((k : K) → ι k) → ℂ) => G y) (↑F : Set ((Fin e → ℂ) → ((k : K) → ι k) → ℂ)) (fibre P Ψ y) := fun G hG => (hFS hG).2.2 y hyb
    have hle := Set.ncard_le_ncard_of_injOn (fun G : ((Fin e → ℂ) → ((k : K) → ι k) → ℂ) => G y) hmaps hinj (hfin y)
    rw [Set.ncard_coe_finset, hFc] at hle
    omega
  have hcover : ball c r ⊆ ⋃ m : ℕ, {y | y ∈ ball c r ∧ (fibre P Ψ y).ncard < m} := fun y hy =>
    Set.mem_iUnion.2 ⟨(fibre P Ψ y).ncard + 1, hy, Nat.lt_succ_self _⟩
  have h0 : volume (ball c r) = 0 := measure_mono_null hcover (measure_iUnion_null key)
  exact (Metric.measure_ball_pos volume c hr).ne' h0
end ReciprocityTheory.ChartRestriction.G.Geo
