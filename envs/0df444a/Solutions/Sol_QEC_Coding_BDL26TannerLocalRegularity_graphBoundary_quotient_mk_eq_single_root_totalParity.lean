-- Prove2me | solution 1 for QEC.Coding.BDL26TannerLocalRegularity.graphBoundary_quotient_mk_eq_single_root_totalParity
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T14:41:34.153542+00:00
-- url     : https://prove2.me/submissions/f44ef490-6755-4af1-b403-4b579c08ca2b

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_TannerSquare
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_LocalRegularity
import Theorems.Thm_QEC_Coding_BDL26TannerLocalRegularity_exists_graphBoundary_eq_add_rootParity

set_option autoImplicit false
open QEC
open QEC.Coding
open QEC.Coding.BDL26TannerLocalRegularity
open Module
open BDL26FiniteAlternatingCore
open BDL26FiniteTannerSquare
universe u
namespace QEC.Coding.BDL26TannerLocalRegularity
theorem _root_.solution
    {Vertex Edge : Type}
    [Fintype Vertex] [Fintype Edge]
    [DecidableEq Vertex] [DecidableEq Edge]
    (edgeStart edgeEnd : Edge → Vertex) (root : Vertex)
    (paths : ∀ vertex, UndirectedPath edgeStart edgeEnd root vertex)
    (word : Word Field Vertex) :
    (LinearMap.range (graphBoundary edgeStart edgeEnd)).mkQ word =
      (LinearMap.range (graphBoundary edgeStart edgeEnd)).mkQ
        (Pi.single root (totalParity word)) := by
  change (Submodule.Quotient.mk word :
      Word Field Vertex ⧸ LinearMap.range (graphBoundary edgeStart edgeEnd)) =
    Submodule.Quotient.mk (Pi.single root (totalParity word))
  rw [Submodule.Quotient.eq]
  obtain ⟨chain, hchain⟩ :=
    exists_graphBoundary_eq_add_rootParity edgeStart edgeEnd root paths word
  refine ⟨chain, ?_⟩
  rw [hchain]
  ext vertex
  change word vertex +
      (Pi.single root (totalParity word) : Word Field Vertex) vertex =
    word vertex -
      (Pi.single root (totalParity word) : Word Field Vertex) vertex
  rw [ZModModule.sub_eq_add]
end QEC.Coding.BDL26TannerLocalRegularity
