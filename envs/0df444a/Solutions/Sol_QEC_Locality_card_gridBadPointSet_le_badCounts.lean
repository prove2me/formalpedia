-- Prove2me | solution 1 for QEC.Locality.card_gridBadPointSet_le_badCounts
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T17:46:45.599129+00:00
-- url     : https://prove2.me/submissions/44046396-bda5-4a58-830b-9bd79d841ebb

import Definitions.Def_QEC_Locality_CorrectableRegions_CorrectableRegionClosure
import Definitions.Def_QEC_Locality_OptimalTradeoff_PackingTiling
import Definitions.Def_QEC_Locality_OptimalTradeoff_RecursivePartition
import Theorems.Thm_QEC_Locality_card_gridBadLongEndpointQubits_le_edgeBadCount

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
attribute [local instance] QEC.Locality.instClassicalDecidableRecursive
namespace QEC.Locality
theorem _root_.solution
    (P : BinaryStabilizerPresentation (ι := ι) (κ := κ))
    (embedding : UnitSeparatedEmbedding2D ι) (threshold w ell : ℝ)
    (t : GridTranslation w) :
    ((gridBadPointSet P embedding threshold w ell t).card : ℝ) ≤
      (vertexBadCount w (2 * ell) embedding.point t : ℝ) +
        (edgeBadCount w (2 * ell)
          (P.daiLiLongIncidencePoint embedding threshold) t : ℝ) := by
  have hunion := Finset.card_union_le
    (Finset.univ.filter fun q => vertexBad w (2 * ell) t (embedding.point q))
    (gridBadLongEndpointQubits P embedding threshold w ell t)
  have hendpoints := card_gridBadLongEndpointQubits_le_edgeBadCount
    P embedding threshold w ell t
  have hunionReal :
      ((gridBadPointSet P embedding threshold w ell t).card : ℝ) ≤
        ((Finset.univ.filter fun q =>
          vertexBad w (2 * ell) t (embedding.point q)).card : ℝ) +
          ((gridBadLongEndpointQubits P embedding threshold w ell t).card : ℝ) := by
    exact_mod_cast hunion
  calc
    _ ≤ ((Finset.univ.filter fun q =>
          vertexBad w (2 * ell) t (embedding.point q)).card : ℝ) +
          ((gridBadLongEndpointQubits P embedding threshold w ell t).card : ℝ) := hunionReal
    _ ≤ (vertexBadCount w (2 * ell) embedding.point t : ℝ) +
        (edgeBadCount w (2 * ell)
          (P.daiLiLongIncidencePoint embedding threshold) t : ℝ) := by
      rw [vertexBadCount]
      gcongr
end QEC.Locality
