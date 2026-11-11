-- Prove2me | solution 1 for QEC.Coding.BDL26RXErrorPullback.inverse_residual_potential
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T10:10:53.346952+00:00
-- url     : https://prove2.me/submissions/60becec9-f8a8-4a22-841f-679627cb3428

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXCohomology_Indexed
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_FiniteCohomology
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXErrorPullback_EmbeddedReadout
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_CanonicalHistoryMarks_Snapshots
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXErrorPullback
import Theorems.Thm_QEC_Coding_BDL26RXErrorPullback_inverse_residual_boundary
import Theorems.Thm_QEC_Coding_BDL26RXErrorPullback_inverse_forward_value
import Theorems.Thm_QEC_Locality_BGKLSeparatorTree_IsNode_trans


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
    ∃ p : Potential S depth i,
      (indexedFamily S depth).coboundary0 i.succ p = fun q =>
        (((indexedDecoderData S depth).selectedMap i).map1
          (inverseCocycle S depth i h w).val) q - w.val q := by
  have hb := inverse_residual_boundary S depth i h w
  change (BDL26FiniteCohomology.stepCocycle S i.val
    (inverseCocycle S depth i h w)).val - w.val ∈
      (BDL26RXCohomology.complex (state S (i.val + 1)).presentation).firstCoboundaryCheckCode.carrier at hb
  obtain ⟨p, hp⟩ := (mem_boundary_iff _ _).mp hb
  refine ⟨p, ?_⟩
  rw [indexedFamily_coboundary0]
  funext q
  have hv := congrFun (inverse_forward_value S depth i (inverseCocycle S depth i h w)) q
  exact (congrFun hp q).trans (congrArg (fun x : ZMod 2 => x - w.val q) hv)
end QEC.Coding.BDL26RXErrorPullback
