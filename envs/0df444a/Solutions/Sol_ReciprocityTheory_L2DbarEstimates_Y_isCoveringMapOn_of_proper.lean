-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.Y.isCoveringMapOn_of_proper
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T16:10:00.256098+00:00
-- url     : https://prove2.me/submissions/dd530455-3742-4566-8a42-bb32e34d2a7e

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_FlatCalc
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_DifferentiableAtLocalCoordinates
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Ck_continuous
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Ck_mono
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Smooth_continuous


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y
open MeasureTheory Filter Topology WeightedAtlas Asymptotics
open scoped ContDiff ENNReal Pointwise Matrix
noncomputable section
universe u
namespace ReciprocityTheory.L2DbarEstimates.Y
theorem _root_.solution {n : ℕ} {E : Type*} [TopologicalSpace E] [T2Space E] (z : E → V n)
    (U : Set (V n)) (hU : IsOpen U) (hz : ∀ x, z x ∈ U) (hl : IsLocalHomeomorph z)
    (hp : ∀ K : Set (V n), IsCompact K → K ⊆ U → IsCompact (z ⁻¹' K)) :
    IsCoveringMapOn z U ∧ ∀ y, (z ⁻¹' {y}).Finite := by
  let g : E → U := fun x => ⟨z x, hz x⟩
  have hgc : Continuous g := hl.continuous.subtype_mk _
  have hgl : IsLocalHomeomorph g :=
    IsLocalHomeomorph.of_comp (g := Subtype.val) (by simpa [Function.comp_def, g] using hl)
      hU.isOpenEmbedding_subtypeVal.isLocalHomeomorph hgc
  have hgp : IsProperMap g := by
    refine isProperMap_iff_isCompact_preimage.2 ⟨hgc, fun K hK => ?_⟩
    have h1 := hp (Subtype.val '' K) (hK.image continuous_subtype_val)
      (by rintro _ ⟨y, -, rfl⟩; exact y.2)
    have h2 : g ⁻¹' K = z ⁻¹' (Subtype.val '' K) := by
      ext x; simp only [Set.mem_preimage, Set.mem_image]
      constructor
      · intro hx; exact ⟨g x, hx, rfl⟩
      · rintro ⟨y, hy, hyx⟩
        have : y = g x := Subtype.ext hyx
        rw [← this]; exact hy
    rw [h2]; exact h1
  have hfib : ∀ y (hy : y ∈ U), (z ⁻¹' {y}).Finite := by
    intro y hy
    have h2 : z ⁻¹' {y} = g ⁻¹' {⟨y, hy⟩} := by
      ext x; simp [g, Subtype.ext_iff]
    rw [h2]
    refine (hgp.isCompact_preimage isCompact_singleton).finite ?_
    refine (hgl.isLocalHomeomorphOn.mono (Set.subset_univ _)).isDiscrete_of_image ?_
    refine (Set.subsingleton_singleton.anti (Set.image_preimage_subset _ _)).isDiscrete
  refine ⟨?_, fun y => ?_⟩
  · refine IsCoveringMapOn.of_isCoveringMap_subtype hU hz ?_
    refine isCoveringMap_iff_isCoveringMapOn_univ.2 ?_
    refine hgp.isClosedMap.isCoveringMapOn_of_isLocalHomeomorphOn (fun x _ => ?_)
      hgl.isLocalHomeomorphOn
    have h2 : g ⁻¹' {x} = z ⁻¹' {(x : V n)} := by
      ext x'; simp [g, Subtype.ext_iff]
    rw [h2]; exact hfib x x.2
  · by_cases hy : y ∈ U
    · exact hfib y hy
    · convert Set.finite_empty
      ext x; simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_empty_iff_false, iff_false]
      intro h; exact hy (h ▸ hz x)
end ReciprocityTheory.L2DbarEstimates.Y
