-- Prove2me | solution 1 for PlaneDrawingDartSectorWitnessDataFromCollarChoices
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-06T07:03:21.683997+00:00
-- url     : https://prove2.me/submissions/61da7060-efde-4873-945c-49aabca88fa6

import Mathlib
import Definitions.Def_OrdinaryPolygonalDrawing
import Definitions.Def_PlaneDrawingDartArcData
import Definitions.Def_PlaneDrawingDartCollarChoiceData
import Definitions.Def_PlaneDrawingDartSectorWitnessData
import Definitions.Def_PlaneDrawingDartSideStripData
import Definitions.Def_PlaneDrawingDartVertexSectorGeometry

open Classical in
theorem solution {V : Type*} [Fintype V]
    (G : SimpleGraph V) [Fintype G.edgeSet] [DecidableRel G.Adj]
    (D : OrdinaryPolygonalDrawing G) (A : PlaneDrawingDartArcData G D)
    (C : PlaneDrawingDartVertexSectorGeometry G D A)
    (P : PlaneDrawingDartCollarChoiceData G D A C)
    (S : PlaneDrawingDartSideStripData G D A C.star)
    (hleft : ∀ d : G.Dart, S.leftSideStrip d = (P.sideStrips d).leftStrip) :
    Nonempty (PlaneDrawingDartSectorWitnessData G D A C.star S) := by
  refine ⟨⟨fun d => ?_, fun v y hv hy hne hc => ?_⟩⟩
  · refine ⟨C.successorSector d, C.successorSector_isOpen d,
      C.successorSector_isConnected d, C.successorSector_subset_localDisk d,
      C.successorSector_subset_complement d, ?_, ?_,
      fun e => C.successorSector_disjoint_radialGerm d e⟩
    · rw [hleft d]; exact P.successorSector_meets_leftStrip d
    · rw [hleft (C.star.successor d)]
      exact P.successorSector_meets_successor_leftStrip d
  · obtain ⟨d, hd, hy'⟩ := C.vertex_sector_coverage v y hv hy hne hc
    subst hd
    refine ⟨d, rfl, C.successorSector d, hy', C.successorSector_isOpen d,
      C.successorSector_isConnected d, C.successorSector_subset_localDisk d,
      C.successorSector_subset_complement d, ?_, ?_,
      fun e => C.successorSector_disjoint_radialGerm d e⟩
    · rw [hleft d]; exact P.successorSector_meets_leftStrip d
    · rw [hleft (C.star.successor d)]
      exact P.successorSector_meets_successor_leftStrip d
