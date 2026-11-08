-- Prove2me | solution 1 for QEC.Coding.BalancedProduct.LPSQuotientTanner.lpsHorizontalSubsystem_blocklength_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T07:45:48.294054+00:00
-- url     : https://prove2.me/submissions/140aa047-00c6-4a76-b637-4fc3b519f658

import Definitions.Def_QEC_Coding_BalancedProduct_Cyclic
import Definitions.Def_QEC_Coding_BalancedProduct_CyclicLocality
import Definitions.Def_QEC_Coding_BalancedProduct_FreeOrbitCoordinates
import Definitions.Def_QEC_Coding_BalancedProduct_LPSTannerExpansion
import Definitions.Def_QEC_Coding_BalancedProduct_PKDistance
import Mathlib.Data.Fintype.EquivFin
import Definitions.Def_QEC_Coding_BalancedProduct_LPSQuotientTanner
import Theorems.Thm_QEC_Coding_BalancedProduct_LPSQuotientTanner_lpsHorizontalSubsystem_blocklength_eq_edge_add_check
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
    Fintype.card
        (LiftedProduct.QubitIndex
          (CheckOrbit401 q) (EdgeOrbit401 q hq) Unit Unit (CyclicGroup q)) =
      401 * Fintype.card (Vertex401 q) := by
  rw [lpsHorizontalSubsystem_blocklength_eq_edge_add_check q hq,
    LPSTannerExpansion.card_edge401_eq q hq40 hq,
    LPSTannerExpansion.card_check401_eq q]
  omega
end QEC.Coding.BalancedProduct.LPSQuotientTanner
