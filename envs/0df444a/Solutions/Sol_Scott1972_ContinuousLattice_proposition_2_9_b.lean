-- Prove2me | solution 1 for Scott1972.ContinuousLattice.proposition_2_9_b
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T05:33:35.999075+00:00
-- url     : https://prove2.me/submissions/57a279e6-c555-4ee9-be56-e5ae465fec0d

import Definitions.Def_Scott1972_ContinuousLattice_MilnerCorrection
import Definitions.Def_Scott1972_ContinuousLattice_ScottMaps
import Definitions.Def_Scott1972_ContinuousLattice_Injective
import Mathlib.Order.Preorder.Finite
import Definitions.Def_Scott1972_ContinuousLattice_Constructions
import Theorems.Thm_Scott1972_ContinuousLattice_proposition_2_9_a
import Theorems.Thm_Scott1972_ContinuousLattice_wayBelow_proj
import Theorems.Thm_Scott1972_ContinuousLattice_wayBelow_finite_support
import Theorems.Thm_Scott1972_ContinuousLattice_continuous_of_preservesDirectedSup
import Theorems.Thm_Scott1972_ContinuousLattice_exists_wayBelow_Ici_subset
import Theorems.Thm_Scott1972_ContinuousLattice_isOpen_iff_scottOpen


set_option autoImplicit true
open Scott1972 Scott1972.ContinuousLattice
open Topology Set
variable {D : Type*} [CompleteLattice D]
namespace Scott1972.ContinuousLattice
theorem _root_.solution {ι : Type*} (E : ι → Type*) [∀ i, CompleteLattice (E i)]
    (hE : ∀ i, IsContinuousLattice (E i)) :
    (scottTopologicalSpace : TopologicalSpace (∀ i, E i)) =
      @Pi.topologicalSpace ι E (fun _ => scottTopologicalSpace) := by
  classical
  have hprod : IsContinuousLattice (∀ i, E i) := proposition_2_9_a E hE
  apply le_antisymm
  · -- Product ⊆ Scott: projections preserve directed suprema, hence are Scott-continuous.
    refine le_iInf fun i => ?_
    rw [← continuous_iff_le_induced]
    exact continuous_of_preservesDirectedSup (fun _ _ _ => sSup_apply_eq_sSup_image)
  · -- Scott ⊆ Product: every Scott-open set is a union of finite product-open boxes.
    intro U hU
    rw [isOpen_iff_scottOpen] at hU
    rw [@isOpen_iff_forall_mem_open _ (@Pi.topologicalSpace ι E (fun _ => scottTopologicalSpace))]
    intro z hz
    obtain ⟨a, haz, haIci⟩ := exists_wayBelow_Ici_subset hprod hU hz
    obtain ⟨F, hF⟩ := wayBelow_finite_support haz
    have hproj : ∀ i, a i ≪ z i := fun i => wayBelow_proj haz i
    choose V hVopen hzV hVsub using hproj
    refine ⟨⋂ i ∈ F, (fun w : ∀ j, E j => w i) ⁻¹' V i, ?_, ?_, ?_⟩
    · -- the box lies inside `↑a ⊆ U`
      intro w hw
      rw [Set.mem_iInter₂] at hw
      refine haIci (Set.mem_Ici.2 fun j => ?_)
      by_cases hjF : j ∈ F
      · exact Set.mem_Ici.1 (hVsub j (hw j hjF))
      · rw [hF j hjF]; exact bot_le
    · -- the box is product-open: a finite intersection of cylinders over Scott-open factors
      refine @isOpen_biInter_finset (∀ j, E j) ι
        (@Pi.topologicalSpace ι E (fun _ => scottTopologicalSpace)) F
        (fun i => (fun w : ∀ j, E j => w i) ⁻¹' V i) (fun i _ => ?_)
      have hVi : @IsOpen (E i) scottTopologicalSpace (V i) := isOpen_iff_scottOpen.mpr (hVopen i)
      have hind : @IsOpen _
          (TopologicalSpace.induced (fun w : ∀ j, E j => w i) scottTopologicalSpace)
          ((fun w : ∀ j, E j => w i) ⁻¹' V i) :=
        (isOpen_induced_iff (t := scottTopologicalSpace)).mpr ⟨V i, hVi, rfl⟩
      exact iInf_le
        (fun i => TopologicalSpace.induced (fun w : ∀ j, E j => w i) scottTopologicalSpace) i _ hind
    · -- the box contains `z`
      rw [Set.mem_iInter₂]
      exact fun i _ => hzV i
end Scott1972.ContinuousLattice
