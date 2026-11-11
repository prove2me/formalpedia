-- Prove2me | solution 1 for QEC.Coding.BDL26RXErrorPullback.inverse_residual_boundary
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T10:03:46.183499+00:00
-- url     : https://prove2.me/submissions/c4683cd9-7d66-44fb-a5ad-58f1c44ef1a3

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXCohomology_Indexed
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_FiniteCohomology
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXErrorPullback_EmbeddedReadout
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_CanonicalHistoryMarks_Snapshots
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXErrorPullback
import Theorems.Thm_QEC_Coding_BDL26RXErrorPullback_inverseCocycle_class
import Theorems.Thm_QEC_Coding_BDL26FiniteCohomology_stepEquiv_mk
import Theorems.Thm_QEC_Coding_BDL26FiniteCohomology_stepEquiv_rx
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
    (BDL26FiniteCohomology.stepCocycle S i.val (inverseCocycle S depth i h w) :
      Cocycle (state S (i.val + 1)).presentation) - w ∈
      (complex (state S (i.val + 1)).presentation).middleCoboundaryInCocycles := by
  let u : BDL26FiniteCohomology.Cocycle S i.val := inverseCocycle S depth i h w
  have hf := BDL26FiniteCohomology.stepEquiv_mk S i.val u
  have hb : (BDL26FiniteCohomology.stepEquiv S i.val).symm
      (BDL26FiniteCohomology.classOf S (i.val + 1) w) =
      BDL26FiniteCohomology.classOf S i.val u := by
    rw [BDL26FiniteCohomology.stepEquiv_rx S i.val h]
    exact (inverseCocycle_class S depth i h w).symm
  apply (Submodule.Quotient.mk_eq_zero _).mp
  change BDL26FiniteCohomology.classOf S (i.val + 1)
    (BDL26FiniteCohomology.stepCocycle S i.val u -
      (w : BDL26FiniteCohomology.Cocycle S (i.val + 1))) = 0
  rw [map_sub, ← hf, ← hb, LinearEquiv.apply_symm_apply, sub_self]
end QEC.Coding.BDL26RXErrorPullback
