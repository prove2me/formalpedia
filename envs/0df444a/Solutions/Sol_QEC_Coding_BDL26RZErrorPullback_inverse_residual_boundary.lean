-- Prove2me | solution 1 for QEC.Coding.BDL26RZErrorPullback.inverse_residual_boundary
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T10:24:56.31582+00:00
-- url     : https://prove2.me/submissions/b480c358-308f-4db4-8d68-3a8737abef6d

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RZCohomology_Indexed
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_FiniteCohomology
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_CanonicalHistoryMarks_Snapshots
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RZErrorPullback
import Theorems.Thm_QEC_Coding_BDL26FiniteCohomology_stepEquiv_rz
import Theorems.Thm_QEC_Coding_BDL26RXCohomology_nextEquiv_mk
import Theorems.Thm_QEC_Coding_BDL26RZCohomology_nextEquiv_mk
import Theorems.Thm_QEC_Coding_BDL26RZCohomology_nextEquiv_symm_mk
import Theorems.Thm_QEC_Locality_NoEdgeBetween_symm


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
    (BDL26FiniteCohomology.stepCocycle S i.val
        (nextBackwardCocycle S i.val (state S i.val) h w) :
      Cocycle (state S (i.val + 1)).presentation) - w ∈
      (BDL26RZCohomology.complex (state S (i.val + 1)).presentation).middleCoboundaryInCocycles := by
  let u : BDL26FiniteCohomology.Cocycle S i.val :=
    nextBackwardCocycle S i.val (state S i.val) h w
  have hf : BDL26FiniteCohomology.stepEquiv S i.val
      (BDL26FiniteCohomology.classOf S i.val u) =
      BDL26FiniteCohomology.classOf S (i.val + 1)
        (BDL26FiniteCohomology.stepCocycle S i.val u) := by
    rw [BDL26FiniteCohomology.stepEquiv_rz S i.val h]
    exact nextEquiv_mk S i.val (state S i.val) h u
  have hb : (BDL26FiniteCohomology.stepEquiv S i.val).symm
      (BDL26FiniteCohomology.classOf S (i.val + 1) w) =
      BDL26FiniteCohomology.classOf S i.val u := by
    rw [BDL26FiniteCohomology.stepEquiv_rz S i.val h]
    exact nextEquiv_symm_mk S i.val (state S i.val) h w
  apply (Submodule.Quotient.mk_eq_zero _).mp
  change BDL26FiniteCohomology.classOf S (i.val + 1)
    (BDL26FiniteCohomology.stepCocycle S i.val u -
      (w : BDL26FiniteCohomology.Cocycle S (i.val + 1))) = 0
  rw [map_sub, ← hf, ← hb, LinearEquiv.apply_symm_apply, sub_self]
end QEC.Coding.BDL26RZErrorPullback
