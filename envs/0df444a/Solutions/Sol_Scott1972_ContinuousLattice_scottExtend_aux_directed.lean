-- Prove2me | solution 1 for Scott1972.ContinuousLattice.scottExtend_aux_directed
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T05:32:11.623944+00:00
-- url     : https://prove2.me/submissions/49d8c4ce-8f83-491a-b114-13c1a95928d1

import Definitions.Def_Scott1972_ContinuousLattice_MilnerCorrection
import Definitions.Def_Scott1972_ContinuousLattice_ScottMaps
import Definitions.Def_Scott1972_ContinuousLattice_Injective
import Mathlib.Order.Preorder.Finite
import Definitions.Def_Scott1972_ContinuousLattice_Constructions

set_option autoImplicit true
open Scott1972 Scott1972.ContinuousLattice
open Topology Set
variable {D : Type*} [CompleteLattice D]
variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {E : Type*} [CompleteLattice E]
namespace Scott1972.ContinuousLattice
theorem _root_.solution (e : X → Y) (f : X → E) (y : Y) :
    DirectedOn (· ≤ ·) {d | ∃ V : Set Y, IsOpen V ∧ y ∈ V ∧ d = sInf (f '' (e ⁻¹' V))} := by
  rintro _ ⟨V₁, hV₁o, hyV₁, rfl⟩ _ ⟨V₂, hV₂o, hyV₂, rfl⟩
  refine ⟨sInf (f '' (e ⁻¹' (V₁ ∩ V₂))), ⟨V₁ ∩ V₂, hV₁o.inter hV₂o, ⟨hyV₁, hyV₂⟩, rfl⟩, ?_, ?_⟩
  · exact sInf_le_sInf (Set.image_mono (Set.preimage_mono Set.inter_subset_left))
  · exact sInf_le_sInf (Set.image_mono (Set.preimage_mono Set.inter_subset_right))
end Scott1972.ContinuousLattice
