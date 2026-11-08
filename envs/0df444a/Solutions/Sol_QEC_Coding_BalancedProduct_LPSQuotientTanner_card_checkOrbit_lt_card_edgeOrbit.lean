-- Prove2me | solution 1 for QEC.Coding.BalancedProduct.LPSQuotientTanner.card_checkOrbit_lt_card_edgeOrbit
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T07:44:39.803189+00:00
-- url     : https://prove2.me/submissions/d50752d2-23e0-45ca-8795-12097893ff6a

import Definitions.Def_QEC_Coding_BalancedProduct_Cyclic
import Definitions.Def_QEC_Coding_BalancedProduct_CyclicLocality
import Definitions.Def_QEC_Coding_BalancedProduct_FreeOrbitCoordinates
import Definitions.Def_QEC_Coding_BalancedProduct_LPSTannerExpansion
import Definitions.Def_QEC_Coding_BalancedProduct_PKDistance
import Mathlib.Data.Fintype.EquivFin
import Definitions.Def_QEC_Coding_BalancedProduct_LPSQuotientTanner
import Theorems.Thm_QEC_Coding_BalancedProduct_LPSTannerExpansion_card_check401_eq
import Theorems.Thm_QEC_Coding_BalancedProduct_LPSTannerExpansion_card_edge401_eq


set_option autoImplicit false
noncomputable section
open scoped MatrixGroups
open QEC QEC.Coding QEC.Coding.BalancedProduct QEC.Coding.BalancedProduct.LPSQuotientTanner
open Classical
open QEC.Coding
open QEC.Coding.BalancedProduct
open Cyclic FreeOrbitCoordinates LPSTanner LPSArithmetic LPSGraph
open PKDistance
set_option maxRecDepth 4000
namespace QEC.Coding.BalancedProduct.LPSQuotientTanner
theorem _root_.solution
    (q : ℕ) [Fact q.Prime]
    (hq40 : 40 < q)
    (hq : legendreSym q 401 = -1) :
    Fintype.card (CheckOrbit401 q) < Fintype.card (EdgeOrbit401 q hq) := by
  letI : NeZero q := ⟨(Fact.out : q.Prime).ne_zero⟩
  have hEdge := Fintype.card_congr
    (freeOrbitEquiv (CyclicGroup q) (Edge401 q hq))
  have hCheck := Fintype.card_congr
    (freeOrbitEquiv (CyclicGroup q) (Check401 q))
  have hActual :
      Fintype.card (Check401 q) < Fintype.card (Edge401 q hq) := by
    rw [LPSTannerExpansion.card_check401_eq q,
      LPSTannerExpansion.card_edge401_eq q hq40 hq]
    have hvpos : 0 < Fintype.card (Vertex401 q) := Fintype.card_pos
    omega
  apply (Nat.mul_lt_mul_right (Fintype.card_pos :
    0 < Fintype.card (CyclicGroup q))).mp
  calc
    Fintype.card (CheckOrbit401 q) * Fintype.card (CyclicGroup q) =
        Fintype.card (CheckOrbit401 q × CyclicGroup q) :=
          (Fintype.card_prod _ _).symm
    _ = Fintype.card (Check401 q) := hCheck.symm
    _ < Fintype.card (Edge401 q hq) := hActual
    _ = Fintype.card (EdgeOrbit401 q hq × CyclicGroup q) := hEdge
    _ = Fintype.card (EdgeOrbit401 q hq) * Fintype.card (CyclicGroup q) :=
      Fintype.card_prod _ _
end QEC.Coding.BalancedProduct.LPSQuotientTanner
