-- Prove2me | solution 1 for QEC.Coding.BalancedProduct.LPSQuotientTanner.cyclic_mul_edgeOrbit_sub_checkOrbit
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T07:55:00.132264+00:00
-- url     : https://prove2.me/submissions/c85f7754-0124-47d6-9405-ae518b017996

import Definitions.Def_QEC_Coding_BalancedProduct_Cyclic
import Definitions.Def_QEC_Coding_BalancedProduct_CyclicLocality
import Definitions.Def_QEC_Coding_BalancedProduct_FreeOrbitCoordinates
import Definitions.Def_QEC_Coding_BalancedProduct_LPSTannerExpansion
import Definitions.Def_QEC_Coding_BalancedProduct_PKDistance
import Mathlib.Data.Fintype.EquivFin
import Definitions.Def_QEC_Coding_BalancedProduct_LPSQuotientTanner
import Theorems.Thm_QEC_Coding_BalancedProduct_LPSQuotientTanner_card_edge401_eq_cyclic_mul_edgeOrbit
import Theorems.Thm_QEC_Coding_BalancedProduct_LPSQuotientTanner_card_check401_eq_cyclic_mul_checkOrbit
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
namespace QEC.Coding.BalancedProduct.LPSQuotientTanner
theorem _root_.solution
    (q : ℕ) [Fact q.Prime]
    (hq40 : 40 < q)
    (hq : legendreSym q 401 = -1) :
    q * (Fintype.card (EdgeOrbit401 q hq) -
        Fintype.card (CheckOrbit401 q)) =
      Fintype.card (Vertex401 q) := by
  rw [Nat.mul_sub_left_distrib,
    ← card_edge401_eq_cyclic_mul_edgeOrbit q hq,
    ← card_check401_eq_cyclic_mul_checkOrbit q,
    LPSTannerExpansion.card_edge401_eq q hq40 hq,
    LPSTannerExpansion.card_check401_eq q]
  omega
end QEC.Coding.BalancedProduct.LPSQuotientTanner
