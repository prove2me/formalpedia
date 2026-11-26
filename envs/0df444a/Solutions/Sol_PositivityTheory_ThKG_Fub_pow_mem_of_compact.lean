-- Prove2me | solution 1 for PositivityTheory.ThKG.Fub.pow_mem_of_compact
-- status  : ACCEPTED   (prove)
-- author  : @martelus trismortuus
-- created : 2026-11-26T03:04:07.521642+00:00
-- url     : https://prove2.me/submissions/4e5cf6e3-5f0a-4ba7-86a9-3ae1f6023fbf

import Mathlib
import Definitions.Def_Development_WeilBound_ThetaLifts_LocalTheory_ConeShifts_FubTate
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PositivityTheory PositivityTheory.ThKG PositivityTheory.ThKG.Fub
open MeasureTheory Topology Filter
theorem _root_.solution {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (U : Subgroup G) (hU : IsOpen (U : Set G))
    {K : Set G} (hK : IsCompact K) {x : G} (hx : ∀ n : ℕ, x ^ n ∈ K) : ∃ k : ℕ, 0 < k ∧ x ^ k ∈ U := by
  have hcov : K ⊆ ⋃ y ∈ K, (fun z => y⁻¹ * z) ⁻¹' (U : Set G) := by
    intro y hy
    exact Set.mem_biUnion hy (by simp)
  obtain ⟨T, hTK, hTfin, hT⟩ := hK.elim_finite_subcover_image (b := K)
    (c := fun y => (fun z => y⁻¹ * z) ⁻¹' (U : Set G)) (fun y _ => hU.preimage (continuous_const_mul _)) hcov
  have hch : ∀ n : ℕ, ∃ y ∈ T, y⁻¹ * x ^ n ∈ U := by
    intro n
    have := hT (hx n)
    simpa only [Set.mem_iUnion, Set.mem_preimage, SetLike.mem_coe, exists_prop] using this
  choose g hgT hg using hch
  have : Finite T := hTfin.to_subtype
  obtain ⟨a, b, hne, hab⟩ := Finite.exists_ne_map_eq_of_infinite (fun n : ℕ => (⟨g n, hgT n⟩ : T))
  have hab' : g a = g b := congrArg Subtype.val hab
  have key : ∀ i j : ℕ, i < j → g i = g j → ∃ k : ℕ, 0 < k ∧ x ^ k ∈ U := by
    intro i j hij h
    refine ⟨j - i, by omega, ?_⟩
    have h1 := U.mul_mem (U.inv_mem (hg i)) (hg j)
    rw [h] at h1
    have : ((g j)⁻¹ * x ^ i)⁻¹ * ((g j)⁻¹ * x ^ j) = x ^ (j - i) := by
      rw [mul_inv_rev, inv_inv, mul_assoc, mul_inv_cancel_left, pow_sub x hij.le]
      exact ((Commute.refl x).pow_pow i j).inv_left.eq
    rwa [this] at h1
  rcases lt_or_gt_of_ne hne with h | h
  · exact key a b h hab'
  · exact key b a h hab'.symm

