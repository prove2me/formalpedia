-- Prove2me | solution 1 for QEC.Coding.BDL26RZErrorPullback.inverse_residual_potential
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T10:30:15.883512+00:00
-- url     : https://prove2.me/submissions/a6a48299-c9c6-43f9-b97d-f66f7e95c2ca

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RZCohomology_Indexed
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_FiniteCohomology
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_CanonicalHistoryMarks_Snapshots
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RZErrorPullback
import Theorems.Thm_QEC_Coding_BDL26RZErrorPullback_inverse_residual_boundary
import Theorems.Thm_QEC_Coding_BDL26RZErrorPullback_inverse_forward_value
import Theorems.Thm_QEC_Locality_BGKLSeparatorTree_IsNode_trans


set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26RZErrorPullback
open Classical BDL26FiniteTannerSquare BDL26DecodingGraph BDL26IndexedDecoder
open BDL26RZMap1CoordinateBridge BDL26RZCohomology BDL26AlternatingCochain
open MultiscaleDecoder BDL26OwnerIncidenceMasks
variable (S : OddScale) (depth : Nat) (i : StepIndex depth)
namespace QEC.Coding.BDL26RZErrorPullback
theorem _root_.solution (h : ¬ i.val % 2 = 0)
    (w : Cocycle (state S (i.val + 1)).presentation) :
    ∃ p : Potential S depth i,
      (indexedFamily S depth).coboundary0 i.succ p = fun q =>
        (((indexedDecoderData S depth).selectedMap i).map1
          (nextBackwardCocycle S i.val (state S i.val) h w).val) q - w.val q := by
  have hb := inverse_residual_boundary S depth i h w
  change (BDL26FiniteCohomology.stepCocycle S i.val
    (nextBackwardCocycle S i.val (state S i.val) h w)).val - w.val ∈
      (BDL26RZCohomology.complex (state S (i.val + 1)).presentation).firstCoboundaryCheckCode.carrier at hb
  obtain ⟨p, hp⟩ := (mem_boundary_iff _ _).mp hb
  refine ⟨p, ?_⟩
  rw [indexedFamily_coboundary0]
  funext q
  have hv := congrFun (inverse_forward_value S depth i
    (nextBackwardCocycle S i.val (state S i.val) h w)) q
  exact (congrFun hp q).trans (congrArg (fun x : ZMod 2 => x - w.val q) hv)
end QEC.Coding.BDL26RZErrorPullback
