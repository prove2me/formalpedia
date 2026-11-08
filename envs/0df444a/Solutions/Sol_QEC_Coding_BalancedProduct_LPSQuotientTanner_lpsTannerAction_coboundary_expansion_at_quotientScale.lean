-- Prove2me | solution 1 for QEC.Coding.BalancedProduct.LPSQuotientTanner.lpsTannerAction_coboundary_expansion_at_quotientScale
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T07:54:39.063082+00:00
-- url     : https://prove2.me/submissions/f82c6bef-5b88-4d2d-ab0f-60713d728aff

import Definitions.Def_QEC_Coding_BalancedProduct_Cyclic
import Definitions.Def_QEC_Coding_BalancedProduct_CyclicLocality
import Definitions.Def_QEC_Coding_BalancedProduct_FreeOrbitCoordinates
import Definitions.Def_QEC_Coding_BalancedProduct_LPSTannerExpansion
import Definitions.Def_QEC_Coding_BalancedProduct_PKDistance
import Mathlib.Data.Fintype.EquivFin
import Definitions.Def_QEC_Coding_BalancedProduct_LPSQuotientTanner
import Theorems.Thm_QEC_Coding_BalancedProduct_LPSQuotientTanner_lpsTannerAction_coboundary_expansion
import Theorems.Thm_QEC_Coding_BalancedProduct_LPSQuotientTanner_card_check401_eq_cyclic_mul_checkOrbit

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
    (tannerAction (LiftedProduct.starTranspose
      (lpsTannerGroupAlgebraMatrix q hq40 hq))).SmallSetExpanding
        (q * (Fintype.card (CheckOrbit401 q) / 10000000)) 11 102500 := by
  have hRelative := lpsTannerAction_coboundary_expansion q hq40 hq hLPS
  refine ⟨hRelative.2.1, ?_⟩
  intro z hz
  apply hRelative.2.2 z
  calc
    10000000 * HammingWeight z ≤
        10000000 * (q * (Fintype.card (CheckOrbit401 q) / 10000000)) :=
      Nat.mul_le_mul_left _ hz
    _ = q * (10000000 *
        (Fintype.card (CheckOrbit401 q) / 10000000)) := by ring
    _ ≤ q * Fintype.card (CheckOrbit401 q) :=
      Nat.mul_le_mul_left q (Nat.mul_div_le _ _)
    _ = Fintype.card (Check401 q) :=
      (card_check401_eq_cyclic_mul_checkOrbit q).symm
    _ = 1 * Fintype.card (CheckOrbit401 q × CyclicGroup q) := by
      rw [one_mul]
      exact Fintype.card_congr
        (freeOrbitEquiv (CyclicGroup q) (Check401 q))
end QEC.Coding.BalancedProduct.LPSQuotientTanner
