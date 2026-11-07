-- Prove2me | solution 1 for QEC.Coding.QuantumTanner.LeftRightCayleySquareComplex.squareGraph_eq_left_right_steps
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T05:14:37.155206+00:00
-- url     : https://prove2.me/submissions/caa0992e-ace9-41a1-986a-a7f284b881d8

import Definitions.Def_QEC_Coding_QuantumTanner_SquareGraph
import Definitions.Def_QEC_Coding_QuantumTanner_CayleyLink
import Definitions.Def_QEC_Coding_QuantumTanner_HeavyEdges
import Definitions.Def_QEC_Coding_ExpanderCodes_SmallSetExpansionOperators
import Definitions.Def_QEC_Coding_QuantumTanner_CayleySquareGraph
import Theorems.Thm_QEC_Coding_QuantumTanner_LeftRightCayleySquareComplex_left_right_step_ne_base
import Theorems.Thm_QEC_Coding_QuantumTanner_LeftRightCayleySquareComplex_incident_link_iff_same_side_corners

set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.QuantumTanner QEC.Coding.QuantumTanner.LeftRightCayleySquareComplex
open Classical QEC.Coding.SmallSetExpansion
universe v
variable {G A B Square : Type v} [Group G] [Fintype G] [Fintype A] [Fintype B]
  [Fintype Square]
namespace QEC.Coding.QuantumTanner.LeftRightCayleySquareComplex
theorem _root_.solution
    (X : LeftRightCayleySquareComplex G A B Square) (hX : X.HasCayleyLinkIdentities)
    (side : Bool) (g h : G) :
    X.squareGraph side g h =
      (Finset.univ.filter fun ab : A × B => X.leftGenerator ab.1 * g * X.rightGenerator ab.2 = h).card := by
  have hSet : (Finset.univ.filter fun q =>
      X.Incident (g, side) q ∧ X.Incident (h, side) q ∧ g ≠ h) =
      (Finset.univ.filter fun ab : A × B =>
        X.leftGenerator ab.1 * g * X.rightGenerator ab.2 = h).image (X.link (g, side)) := by
    ext q
    constructor
    · intro hq
      obtain ⟨hg, hh, hne⟩ := (Finset.mem_filter.mp hq).2
      obtain ⟨⟨a, b⟩, rfl⟩ := hg
      have hCorner := (X.incident_link_iff_same_side_corners hX g h side a b).mp hh
      refine Finset.mem_image.mpr ⟨(a, b), Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, rfl⟩
      exact (hCorner.resolve_left hne.symm).symm
    · intro hq
      obtain ⟨⟨a, b⟩, hab, rfl⟩ := Finset.mem_image.mp hq
      have hStep := (Finset.mem_filter.mp hab).2
      refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ⟨(a, b), rfl⟩, ?_, ?_⟩
      · exact (X.incident_link_iff_same_side_corners hX g h side a b).mpr (Or.inr hStep.symm)
      · rw [← hStep]
        exact (X.left_right_step_ne_base g a b).symm
  unfold squareGraph
  rw [hSet, Finset.card_image_of_injective _ (X.link_injective (g, side))]
end QEC.Coding.QuantumTanner.LeftRightCayleySquareComplex
