-- Prove2me | solution 1 for ReciprocityTheory.DiscreteGroups.LocalClassField.Deg2.norm_all
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T14:32:57.850481+00:00
-- url     : https://prove2.me/submissions/d67f57f3-445c-4d61-916b-fd43395ec310

import Mathlib
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_IsTwoCocycleCoboundary
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_CurriedCoboundaryEq
import Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_Deg2_d_sub_d
import Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_Deg2_norm0
import Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_Deg2_normA
import Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_Deg2_normB

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.DiscreteGroups ReciprocityTheory.DiscreteGroups.LocalClassField ReciprocityTheory.DiscreteGroups.LocalClassField.Deg2
open ReciprocityTheory.Coh ReciprocityTheory.Coh.InflationRestrictionInvariants ReciprocityTheory.Coh.CohomologyFunctoriality₂ ReciprocityTheory.Gal Cx Function
noncomputable section
universe u
variable {R : Type u} [CommRing R] {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable (M : TRep R G) (N : Subgroup G)
namespace ReciprocityTheory.DiscreteGroups.LocalClassField.Deg2
theorem _root_.solution [N.Normal] (hN : IsOpen (N : Set G)) (h1 : Subsingleton ((M.resSub N).H 1)) (x : M.coch.X 2)
    (hx : M.coch.d 2 x = 0)
    (hres : (Pair.res M N.subtype continuous_subtype_val).hom.f 2 x ∈ (M.resSub N).coch.B 2) :
    ∃ w : M.coch.X 1, ∀ n ∈ N, ∀ g, cur M (x - M.coch.d 1 w) n g = 0 ∧ cur M (x - M.coch.d 1 w) g n = 0 := by
  obtain ⟨w0, h0⟩ := norm0 M N hN x hres
  obtain ⟨w1, hA⟩ := normA M N hN _ (d_sub_d M x hx w0) h0
  obtain ⟨w2, hB⟩ := normB M N hN h1 _ (d_sub_d M _ (d_sub_d M x hx w0) w1) hA
  refine ⟨w0 + w1 + w2, ?_⟩
  have : x - M.coch.d 1 (w0 + w1 + w2) = x - M.coch.d 1 w0 - M.coch.d 1 w1 - M.coch.d 1 w2 := by
    rw [map_add, map_add]; abel
  rw [this]
  exact hB
end ReciprocityTheory.DiscreteGroups.LocalClassField.Deg2
