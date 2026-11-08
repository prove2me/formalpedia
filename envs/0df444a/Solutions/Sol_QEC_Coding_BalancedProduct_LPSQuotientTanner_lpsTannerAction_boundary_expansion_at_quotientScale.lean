-- Prove2me | solution 1 for QEC.Coding.BalancedProduct.LPSQuotientTanner.lpsTannerAction_boundary_expansion_at_quotientScale
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T07:59:13.666082+00:00
-- url     : https://prove2.me/submissions/078343d6-aab0-47f9-a0c8-59a502fc9e16

import Definitions.Def_QEC_Coding_BalancedProduct_Cyclic
import Definitions.Def_QEC_Coding_BalancedProduct_CyclicLocality
import Definitions.Def_QEC_Coding_BalancedProduct_FreeOrbitCoordinates
import Definitions.Def_QEC_Coding_BalancedProduct_LPSTannerExpansion
import Definitions.Def_QEC_Coding_BalancedProduct_PKDistance
import Mathlib.Data.Fintype.EquivFin
import Definitions.Def_QEC_Coding_BalancedProduct_LPSQuotientTanner
import Theorems.Thm_QEC_Coding_BalancedProduct_LPSQuotientTanner_lpsTannerAction_boundary_expansion
import Theorems.Thm_QEC_Coding_BalancedProduct_LPSQuotientTanner_card_edge401_eq_cyclic_mul_edgeOrbit

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
    (hLPS : LPS401RayleighBound q hq) :
    (tannerAction (lpsTannerGroupAlgebraMatrix q hq40 hq)).SmallSetExpanding
      (q * (Fintype.card (EdgeOrbit401 q hq) / 10000000)) 44 41123 := by
  have hRelative := lpsTannerAction_boundary_expansion q hq40 hq hLPS
  refine ⟨hRelative.2.1, ?_⟩
  intro z hz
  apply hRelative.2.2 z
  calc
    10000000 * HammingWeight z ≤
        10000000 * (q * (Fintype.card (EdgeOrbit401 q hq) / 10000000)) :=
      Nat.mul_le_mul_left _ hz
    _ = q * (10000000 *
        (Fintype.card (EdgeOrbit401 q hq) / 10000000)) := by ring
    _ ≤ q * Fintype.card (EdgeOrbit401 q hq) :=
      Nat.mul_le_mul_left q (Nat.mul_div_le _ _)
    _ = Fintype.card (Edge401 q hq) :=
      (card_edge401_eq_cyclic_mul_edgeOrbit q hq).symm
    _ = 1 * Fintype.card (EdgeOrbit401 q hq × CyclicGroup q) := by
      rw [one_mul]
      exact Fintype.card_congr
        (freeOrbitEquiv (CyclicGroup q) (Edge401 q hq))
end QEC.Coding.BalancedProduct.LPSQuotientTanner
