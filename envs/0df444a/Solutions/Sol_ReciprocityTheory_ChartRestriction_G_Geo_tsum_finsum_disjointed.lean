-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Geo.tsum_finsum_disjointed
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T13:06:29.380235+00:00
-- url     : https://prove2.me/submissions/a567c7fc-c478-4250-96a5-f2f004656623

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterBridgeG

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
open MeasureTheory Set Filter Topology Function
variable {e : ℕ}
namespace ReciprocityTheory.ChartRestriction.G.Geo
theorem _root_.solution {α : Type*} {D : ℕ → Set α} (hd : Pairwise (Disjoint on D))
    {O : Set α} (hU : ⋃ n, D n = O) {G : Set α} (hG : (O ∩ G).Finite) (f : α → ℝ) :
    ∑' n, ∑ᶠ u ∈ D n ∩ G, f u = ∑ᶠ u ∈ O ∩ G, f u := by
  classical
  have hsub : ∀ n, D n ⊆ O := fun n => hU ▸ subset_iUnion D n
  have hterm : ∀ n, ∑ᶠ u ∈ D n ∩ G, f u = ∑ u ∈ hG.toFinset, if u ∈ D n then f u else 0 := by
    intro n
    rw [finsum_mem_eq_finite_toFinset_sum f (hG.subset fun u hu => ⟨hsub n hu.1, hu.2⟩),
      Finset.sum_ite, Finset.sum_const_zero, add_zero]
    congr 1
    ext u
    simp only [Finite.mem_toFinset, Finset.mem_filter, mem_inter_iff]
    exact ⟨fun h => ⟨⟨hsub n h.1, h.2⟩, h.1⟩, fun h => ⟨h.2, h.1.2⟩⟩
  have hfun : ∀ u ∈ hG.toFinset, ∃ n0 : ℕ,
      (fun n => if u ∈ D n then f u else 0) = fun n => if n = n0 then f u else 0 := by
    intro u hu
    have huO : u ∈ O := (hG.mem_toFinset.mp hu).1
    obtain ⟨n0, hn0⟩ := mem_iUnion.mp (hU ▸ huO : u ∈ ⋃ n, D n)
    refine ⟨n0, funext fun n => ?_⟩
    by_cases hn : n = n0
    · subst hn; simp [hn0]
    · have : u ∉ D n := fun h => (hd hn).le_bot ⟨h, hn0⟩
      simp [this, hn]
  simp_rw [hterm]
  rw [Summable.tsum_finsetSum (fun u hu => ?_), finsum_mem_eq_finite_toFinset_sum f hG]
  · refine Finset.sum_congr rfl fun u hu => ?_
    obtain ⟨n0, h⟩ := hfun u hu
    rw [h, tsum_ite_eq]
  · obtain ⟨n0, h⟩ := hfun u hu
    rw [h]
    exact (hasSum_ite_eq n0 (f u)).summable
end ReciprocityTheory.ChartRestriction.G.Geo
