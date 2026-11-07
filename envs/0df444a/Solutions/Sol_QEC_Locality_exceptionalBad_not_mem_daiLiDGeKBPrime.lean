-- Prove2me | solution 1 for QEC.Locality.exceptionalBad_not_mem_daiLiDGeKBPrime
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T14:25:33.342001+00:00
-- url     : https://prove2.me/submissions/1198a862-716f-4e70-85ba-0bd7c0269cab

import Definitions.Def_QEC_Locality_OptimalTradeoff_CorrectablePartition
import Definitions.Def_QEC_Locality_OptimalTradeoff_DistancePartition
import Theorems.Thm_QEC_Locality_mem_daiLiDGeKBPrimeBadEndpoints_of_mem_wide_longEndpoint

set_option autoImplicit false
noncomputable section
open MeasureTheory Set Metric
open QEC QEC.Locality
open QEC Semantics Coding PauliSymplectic
open Coding.StabilizerCode
open Coding.StabilizerCode.BinaryStabilizerPresentation
universe u v
variable {ι : Type u} [Fintype ι] [DecidableEq ι]
variable {κ : Type v} [Fintype κ]
attribute [local instance] QEC.Locality.instClassicalDecidableDGeK
namespace QEC.Locality
theorem _root_.solution
    (P : BinaryStabilizerPresentation (ι := ι) (κ := κ))
    (embedding : UnitSeparatedEmbedding2D ι) (threshold w ell : ℝ)
    (t : GridTranslation w) (q : ι)
    (hq : q ∈ daiLiDGeKExceptionalBadQubits P embedding threshold w ell t) :
    q ∉ daiLiDGeKBPrimeQubits embedding w ell t := by
  intro hWide
  have hLong : q ∈ longInteractionEndpointQubits P embedding threshold :=
    (Finset.mem_sdiff.mp hq).1
  have hBad : q ∈ daiLiDGeKBPrimeBadEndpoints P embedding threshold w ell t :=
    mem_daiLiDGeKBPrimeBadEndpoints_of_mem_wide_longEndpoint P embedding threshold
      w ell t q hWide hLong
  have hCrossing : q ∈ daiLiDGeKCrossingEndpoints P embedding threshold w ell t := by
    exact Finset.mem_union_left _ hBad
  exact (Finset.mem_sdiff.mp hq).2 (Finset.mem_union_right _ hCrossing)
end QEC.Locality
