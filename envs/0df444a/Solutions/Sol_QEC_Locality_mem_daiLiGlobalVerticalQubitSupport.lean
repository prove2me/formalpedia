-- Prove2me | solution 1 for QEC.Locality.mem_daiLiGlobalVerticalQubitSupport
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T21:20:02.468136+00:00
-- url     : https://prove2.me/submissions/b552f156-996d-4061-a72e-1a533f339f82

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
namespace QEC.Locality
theorem _root_.solution
    (embedding : UnitSeparatedEmbedding2D ι) (q : ι) :
    (embedding.point q).2 ∈ daiLiGlobalVerticalQubitSupport embedding := by
  exact Finset.mem_image.mpr ⟨q, Finset.mem_univ q, rfl⟩
end QEC.Locality
