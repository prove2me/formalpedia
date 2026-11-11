-- Prove2me | solution 1 for QEC.Coding.BDL26RXErrorPullback.inverseCocycle_class
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T09:58:24.457225+00:00
-- url     : https://prove2.me/submissions/eded8130-a5f3-425e-bedf-0bb157cd6839

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXCohomology_Indexed
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_FiniteCohomology
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXErrorPullback_EmbeddedReadout
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_CanonicalHistoryMarks_Snapshots
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXErrorPullback
import Theorems.Thm_QEC_Locality_NoEdgeBetween_symm


set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26RXErrorPullback
open Classical BDL26FiniteTannerSquare BDL26DecodingGraph BDL26IndexedDecoder
open BDL26RZMap1CoordinateBridge BDL26RXCohomology BDL26AlternatingCochain
open BDL26RZCohomology (mem_cocycle_iff mem_boundary_iff)
open MultiscaleDecoder BDL26OwnerIncidenceMasks
variable (S : OddScale) (depth : Nat) (i : StepIndex depth)
namespace QEC.Coding.BDL26RXErrorPullback
theorem _root_.solution (h : i.val % 2 = 0)
    (w : Cocycle (state S (i.val + 1)).presentation) :
    classOf (state S i.val).presentation (inverseCocycle S depth i h w) =
      (nextEquiv S i.val (state S i.val) h).symm
        (classOf (state S (i.val + 1)).presentation w) :=
  Classical.choose_spec ((complex (state S i.val).presentation).middleCoboundaryInCocycles.mkQ_surjective
    ((nextEquiv S i.val (state S i.val) h).symm
      (classOf (state S (i.val + 1)).presentation w)))
end QEC.Coding.BDL26RXErrorPullback
