-- Prove2me | solution 2 for QEC.Locality.gridInterior_edge_vertex_cover
-- status  : ACCEPTED   (prove)
-- author  : @Secousses
-- created : 2026-11-05T22:29:59.465104+00:00
-- url     : https://prove2.me/submissions/f8bc8830-78fd-4495-ac50-844a07bcb695

import Definitions.Def_QEC_Locality_CorrectableRegions_CorrectableRegionClosure
import Definitions.Def_QEC_Locality_OptimalTradeoff_PackingTiling
import Definitions.Def_QEC_Locality_OptimalTradeoff_RecursivePartition
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

theorem solution
    (embedding : UnitSeparatedEmbedding2D ι) (w ell : ℝ)
    (t : GridTranslation w) :
    gridInteriorQubits embedding w ell t ∪
        gridEdgeBufferQubits embedding w ell t ∪
        gridVertexBufferQubits embedding w ell t = Finset.univ := by
  ext q
  simp only [gridInteriorQubits, gridEdgeBufferQubits, gridVertexBufferQubits, Finset.mem_union,
    Finset.mem_filter, Finset.mem_univ, true_and, iff_true]
  tauto
