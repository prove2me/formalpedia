-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Sh.pt_degree_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T13:28:30.553351+00:00
-- url     : https://prove2.me/submissions/aaebd9e0-bfcb-45cd-afbe-f64a29d6278f

import Mathlib
import Definitions.Def_ReciprocityTheory_DualLattices_VEqZeroOfPowEqOne
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_WeightedSumBounds_PtOrderProdSub
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_WeightedSumBounds_PtCoeffSingleSubst
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Sh_PTAgree_symm


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Sh
open MvPowerSeries ReciprocityTheory.PGsh
open Classical
noncomputable section
variable {R : Type*} [CommRing R]
namespace ReciprocityTheory.ChartRestriction.G.Sh
theorem _root_.solution {σ : Type*} {α : σ →₀ ℕ} (h : α.degree = 1) :
    ∃ s, α = Finsupp.single s 1 := by
  classical
  have hsum : ∑ i ∈ α.support, α i = 1 := h
  obtain ⟨s, hs⟩ : α.support.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro he
    rw [he, Finset.sum_empty] at hsum
    exact zero_ne_one hsum
  refine ⟨s, ?_⟩
  have hs0 : α s ≠ 0 := Finsupp.mem_support_iff.mp hs
  ext t
  by_cases hts : t = s
  · subst hts
    rw [Finsupp.single_eq_same]
    have h1 : α t ≤ ∑ i ∈ α.support, α i :=
      Finset.single_le_sum (f := fun i => α i) (fun _ _ => Nat.zero_le _) hs
    omega
  · have hst : s ≠ t := Ne.symm hts
    simp only [Finsupp.single_apply, hst, hts, if_false]
    by_contra hne
    have ht : t ∈ α.support := Finsupp.mem_support_iff.mpr hne
    have hsub : ({s, t} : Finset _) ⊆ α.support := by
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl <;> assumption
    have h2 := Finset.sum_le_sum_of_subset (f := fun i => α i) hsub
    rw [Finset.sum_pair hst] at h2
    omega
end ReciprocityTheory.ChartRestriction.G.Sh
