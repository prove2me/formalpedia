-- Prove2me | solution 1 for QEC.Coding.BalancedProduct.LPSQuotientTanner.edgeLocalCoordinate_smul
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T07:41:05.498003+00:00
-- url     : https://prove2.me/submissions/0ea26b62-70bf-44d8-99c7-a5319f4aa99f

import Definitions.Def_QEC_Coding_BalancedProduct_Cyclic
import Definitions.Def_QEC_Coding_BalancedProduct_CyclicLocality
import Definitions.Def_QEC_Coding_BalancedProduct_FreeOrbitCoordinates
import Definitions.Def_QEC_Coding_BalancedProduct_LPSTannerExpansion
import Definitions.Def_QEC_Coding_BalancedProduct_PKDistance
import Mathlib.Data.Fintype.EquivFin
import Definitions.Def_QEC_Coding_BalancedProduct_LPSQuotientTanner

set_option autoImplicit false
noncomputable section
open scoped MatrixGroups
open QEC QEC.Coding QEC.Coding.BalancedProduct QEC.Coding.BalancedProduct.LPSQuotientTanner
open Classical
open QEC.Coding
open QEC.Coding.BalancedProduct
open Cyclic FreeOrbitCoordinates LPSTanner LPSArithmetic LPSGraph
open PKDistance
namespace QEC.Coding.BalancedProduct.LPSQuotientTanner
theorem _root_.solution
    (q : ℕ) [Fact q.Prime]
    (hq40 : 40 < q)
    (hq : legendreSym q 401 = -1)
    (h : CyclicGroup q) (e : Edge401 q hq) (g : Vertex401 q)
    (hg : g ∈ e.1) :
    edgeLocalCoordinate q hq40 hq (h • e) (h • g)
        ((mem_smul_edge_iff q hq h e g).2 hg) =
      edgeLocalCoordinate q hq40 hq e g hg := by
  let X := lpsCayleyGraph401 q hq
  let u := cyclicUpperHom q h
  let i := edgeAsIncident q hq e g hg
  let hg' := (mem_smul_edge_iff q hq h e g).2 hg
  let i' := edgeAsIncident q hq (h • e) (h • g) hg'
  let E := X.incidenceSetEquivNeighborSet g
  let E' := X.incidenceSetEquivNeighborSet (h • g)
  let w := E i
  have hw' : X.Adj (h • g) (w.1 * u) := by
    exact (lpsCayleyGraph401_adj_mul_right_iff q hq g w.1 u).2 w.2
  let w' : X.neighborSet (h • g) := ⟨w.1 * u, hw'⟩
  have hEi : E' i' = w' := by
    have horiginal : s(g, w.1) = e.1 := by
      have hs := congrArg Subtype.val (E.symm_apply_apply i)
      exact hs
    have htransport : s(h • g, w.1 * u) = (h • e).1 := by
      rw [cyclic_smul_vertex, cyclic_smul_edge_val, ← horiginal,
        Sym2.map_mk]
      rfl
    have hinv : E'.symm w' = i' := by
      apply Subtype.ext
      exact htransport
    calc
      E' i' = E' (E'.symm w') := congrArg E' hinv.symm
      _ = w' := E'.apply_symm_apply w'
  let s0 := incidentGeneratorEquiv q hq g i
  have hs0 : generatorNeighborEquiv q hq (h • g) s0 = w' := by
    apply Subtype.ext
    have hs0old : generatorNeighborEquiv q hq g s0 = w := by
      exact (generatorNeighborEquiv q hq g).apply_symm_apply w
    have hs0val := congrArg Subtype.val hs0old
    change s0.1 * g = w.1 at hs0val
    change s0.1 * (g * u) = w.1 * u
    rw [← mul_assoc, hs0val]
  have hgen : incidentGeneratorEquiv q hq (h • g) i' = s0 := by
    change (generatorNeighborEquiv q hq (h • g)).symm (E' i') = s0
    rw [hEi, ← hs0]
    exact (generatorNeighborEquiv q hq (h • g)).symm_apply_apply s0
  change generatorCoordinateEquiv q hq40 hq
      (incidentGeneratorEquiv q hq (h • g) i') =
    generatorCoordinateEquiv q hq40 hq (incidentGeneratorEquiv q hq g i)
  exact congrArg (generatorCoordinateEquiv q hq40 hq) hgen
end QEC.Coding.BalancedProduct.LPSQuotientTanner
