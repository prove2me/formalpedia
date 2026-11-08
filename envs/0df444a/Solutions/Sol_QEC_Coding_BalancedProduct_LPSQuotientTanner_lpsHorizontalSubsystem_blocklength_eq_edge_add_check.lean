-- Prove2me | solution 1 for QEC.Coding.BalancedProduct.LPSQuotientTanner.lpsHorizontalSubsystem_blocklength_eq_edge_add_check
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T07:41:34.202264+00:00
-- url     : https://prove2.me/submissions/f8ede81b-0e23-4b64-a26c-bb9849c2ec85

import Definitions.Def_QEC_Coding_BalancedProduct_Cyclic
import Definitions.Def_QEC_Coding_BalancedProduct_CyclicLocality
import Definitions.Def_QEC_Coding_BalancedProduct_FreeOrbitCoordinates
import Definitions.Def_QEC_Coding_BalancedProduct_LPSTannerExpansion
import Definitions.Def_QEC_Coding_BalancedProduct_PKDistance
import Mathlib.Data.Fintype.EquivFin
import Definitions.Def_QEC_Coding_BalancedProduct_LPSQuotientTanner
import Theorems.Thm_QEC_Coding_BalancedProduct_LPSQuotientTanner_card_edge401_eq_cyclic_mul_edgeOrbit
import Theorems.Thm_QEC_Coding_BalancedProduct_LPSQuotientTanner_card_check401_eq_cyclic_mul_checkOrbit
import Theorems.Thm_QEC_Coding_BalancedProduct_Cyclic_card_qubitIndex
import Theorems.Thm_QEC_Coding_FiberBundle_card_qubitIndex
import Theorems.Thm_QEC_Coding_LiftedProduct_card_qubitIndex


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
    (hq : legendreSym q 401 = -1) :
    Fintype.card
        (LiftedProduct.QubitIndex
          (CheckOrbit401 q) (EdgeOrbit401 q hq) Unit Unit (CyclicGroup q)) =
      Fintype.card (Edge401 q hq) + Fintype.card (Check401 q) := by
  letI : NeZero q := ⟨(Fact.out : q.Prime).ne_zero⟩
  rw [Cyclic.card_qubitIndex, Nat.mul_add,
    ← card_edge401_eq_cyclic_mul_edgeOrbit q hq,
    ← card_check401_eq_cyclic_mul_checkOrbit q]
end QEC.Coding.BalancedProduct.LPSQuotientTanner
