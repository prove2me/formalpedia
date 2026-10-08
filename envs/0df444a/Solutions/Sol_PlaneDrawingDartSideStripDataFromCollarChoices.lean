-- Prove2me | solution 1 for PlaneDrawingDartSideStripDataFromCollarChoices
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-06T05:45:08.397821+00:00
-- url     : https://prove2.me/submissions/4a73d8ed-132c-4a6b-92b4-6446604f4790

import Mathlib
import Definitions.Def_OrdinaryPolygonalDrawing
import Definitions.Def_PlaneDrawingDartArcData
import Definitions.Def_PlaneDrawingDartCollarChoiceData
import Definitions.Def_PlaneDrawingDartSideStripData
import Definitions.Def_PlaneDrawingDartVertexSectorGeometry

set_option autoImplicit false

open Classical
noncomputable section

theorem SSDFCC_existsUnique_component (K S : Set (EuclideanSpace ℝ (Fin 2)))
    (hS : IsConnected S) (hK : S ⊆ Kᶜ) :
    ∃! L : Set (EuclideanSpace ℝ (Fin 2)), ComplementComponent K L ∧ S ⊆ L := by
  obtain ⟨x, hx⟩ := hS.nonempty
  have hxK : x ∈ Kᶜ := hK hx
  refine ⟨connectedComponentIn Kᶜ x, ⟨⟨⟨x, mem_connectedComponentIn hxK⟩,
      connectedComponentIn_subset _ _, isConnected_connectedComponentIn_iff.mpr hxK, ?_⟩,
      hS.isPreconnected.subset_connectedComponentIn hx hK⟩, ?_⟩
  · intro C _ hCK hCc hFC
    exact hCc.isPreconnected.subset_connectedComponentIn
      (hFC (mem_connectedComponentIn hxK)) hCK
  · rintro L ⟨⟨_, hLK, hLc, hLmax⟩, hSL⟩
    apply le_antisymm
    · exact hLc.isPreconnected.subset_connectedComponentIn (hSL hx) hLK
    · exact hLmax _ ⟨x, mem_connectedComponentIn hxK⟩ (connectedComponentIn_subset _ _)
        (isConnected_connectedComponentIn_iff.mpr hxK)
        (hLc.isPreconnected.subset_connectedComponentIn (hSL hx) hLK)

theorem solution {V : Type*} [Fintype V]
    (G : SimpleGraph V) [Fintype G.edgeSet] [DecidableRel G.Adj]
    (D : OrdinaryPolygonalDrawing G) (A : PlaneDrawingDartArcData G D)
    (C : PlaneDrawingDartVertexSectorGeometry G D A)
    (P : PlaneDrawingDartCollarChoiceData G D A C) :
    ∃ S : PlaneDrawingDartSideStripData G D A C.star,
      (∀ d : G.Dart, S.leftSideStrip d = (P.sideStrips d).leftStrip) ∧
        (∀ d : G.Dart, S.rightSideStrip d = (P.sideStrips d).rightStrip) := by
  have hR : ∀ d : G.Dart, (P.sideStrips d).rightStrip ⊆ (OrdinaryDrawingImage G D)ᶜ := by
    intro d
    rw [P.rightStrip_eq_leftStrip_symm d]
    exact P.leftStrip_subset_complement d.symm
  refine ⟨{
    leftSideStrip := fun d => (P.sideStrips d).leftStrip
    rightSideStrip := fun d => (P.sideStrips d).rightStrip
    sideStripData := fun d => ⟨P.sideStrips d, rfl, rfl⟩
    rightSideStrip_eq_leftSideStrip_symm := fun d => P.rightStrip_eq_leftStrip_symm d
    leftSideStrip_subset_complement := fun d => P.leftStrip_subset_complement d
    rightSideStrip_subset_complement := hR
    localComplement_subset_sideStrips := fun d x hx => P.localComplement_subset_sideStrips d x hx
    leftSide_unique_face_component := fun d =>
      SSDFCC_existsUnique_component _ _ (P.sideStrips d).left_connected
        (P.leftStrip_subset_complement d)
    rightSide_unique_face_component := fun d =>
      SSDFCC_existsUnique_component _ _ (P.sideStrips d).right_connected (hR d) },
    fun d => rfl, fun d => rfl⟩
