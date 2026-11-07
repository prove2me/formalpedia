-- Prove2me | solution 1 for QEC.Locality.mem_daiLiTenthCore_rectangle
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T14:27:13.271276+00:00
-- url     : https://prove2.me/submissions/fffbe616-1bff-4a32-a3e1-c1a42d917d90

import Definitions.Def_QEC_Locality_OptimalTradeoff_RecursivePartition
import Definitions.Def_QEC_Locality_OptimalTradeoff_BadSquareSubdivision
import Definitions.Def_QEC_Locality_CorrectableRegions_TwoCorrectableRegionsDimension
import Definitions.Def_QEC_Locality_OptimalTradeoff_LargeDistanceSeparator

set_option autoImplicit false
noncomputable section
open QEC QEC.Locality
open QEC Semantics Coding PauliSymplectic
open Coding.StabilizerCode
open Coding.StabilizerCode.BinaryStabilizerPresentation
universe u v
variable {ι : Type u} [Fintype ι] [DecidableEq ι]
variable {κ : Type v} [Fintype κ]
omit [Fintype ι] [DecidableEq ι]
namespace QEC.Locality
theorem _root_.solution
    (embedding : UnitSeparatedEmbedding2D ι) (region : Finset ι)
    (hRegion : region.Nonempty) {q : ι}
    (hq : q ∈ daiLiTenthCore embedding region hRegion) :
    embedding.point q ∈ rectangle
      (daiLiTenthCoreLower embedding region hRegion)
      (daiLiTenthCoreUpper embedding region hRegion) := by
  rcases Finset.mem_filter.mp hq with ⟨_, hxLower, hxUpper, hyLower, hyUpper⟩
  exact ⟨⟨hxLower, hxUpper⟩, ⟨hyLower, hyUpper⟩⟩
end QEC.Locality
