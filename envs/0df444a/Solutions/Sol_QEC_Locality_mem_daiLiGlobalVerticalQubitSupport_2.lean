-- Prove2me | solution 2 for QEC.Locality.mem_daiLiGlobalVerticalQubitSupport
-- status  : ACCEPTED   (prove)
-- author  : @Secousses
-- created : 2026-11-05T22:29:48.963207+00:00
-- url     : https://prove2.me/submissions/3bf7bba0-a1c4-4651-9bf2-5379b6cd7fbc

import Definitions.Def_QEC_Locality_OptimalTradeoff_RecursivePartition
import Definitions.Def_QEC_Locality_OptimalTradeoff_BadSquareSubdivision
set_option autoImplicit false
noncomputable section
open QEC QEC.Locality
open QEC Semantics Coding PauliSymplectic
open Coding.StabilizerCode
open Coding.StabilizerCode.BinaryStabilizerPresentation
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {κ : Type*} [Fintype κ]

theorem solution
    (embedding : UnitSeparatedEmbedding2D ι) (q : ι) :
    (embedding.point q).2 ∈ daiLiGlobalVerticalQubitSupport embedding := by
  unfold daiLiGlobalVerticalQubitSupport
  exact Finset.mem_image.2 ⟨q, Finset.mem_univ _, rfl⟩
